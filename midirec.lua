-- midirec
-- record + play midi
--
-- E1 select take
-- K2 play / stop
-- K3 record / stop
-- E2 scrub (not rec)
-- E3 loop on / off
--
-- params: in/out port, loop,
-- echo rec / standby / play

local recfile = include("midirec/lib/recfile")

local DATA_DIR = _path.data .. "midirec/"

local midi_in
local midi_out

local state = "stop" -- "stop" | "rec" | "play"

local events = {}    -- {t = seconds, data = {bytes...}}
local len = 0        -- take length in seconds

local rec_start = 0
local play_pos = 0
local play_idx = 1
local play_clock
local screen_metro

local takes = {}     -- list of filenames in DATA_DIR
local take_sel = 1
local dirty = false  -- unsaved recording

local notes_on = {}  -- [ch][note] = true, for panic on stop
local last_out = -1  -- util.time() of last outgoing message

-- helpers -------------------------------------------------------------

local function fmt_time(s)
  s = math.max(0, s)
  return string.format("%d:%05.2f", math.floor(s / 60), s % 60)
end

local function scan_takes()
  takes = {}
  local p = io.popen("ls -1 " .. DATA_DIR .. " 2>/dev/null")
  if p then
    for line in p:lines() do
      if line:match("%.mrec$") then takes[#takes + 1] = line end
    end
    p:close()
  end
  table.sort(takes)
  take_sel = util.clamp(take_sel, 1, math.max(1, #takes))
end

local function next_take_name()
  local n = 1
  while true do
    local name = string.format("take-%03d.mrec", n)
    if not util.file_exists(DATA_DIR .. name) then return name end
    n = n + 1
  end
end

-- some virtual midi ports (the nbout mod, which exposes nb voices as a port
-- named "nb") implement only the named methods -- note_on, note_off, cc --
-- and leave :send() an empty stub. raw bytes sent to those ports vanish with
-- no error. so dispatch by message type instead of sending bytes: that path
-- works for real hardware ports too, since norns' own Midi:note_on and
-- friends just build a message and call :send() internally.
local function send(data)
  if midi_out then
    local m = midi.to_msg(data)
    local t = m and m.type
    if t == "note_on" then
      -- a note_on with velocity 0 is a note_off on many controllers. send it
      -- as a real note_off so ports that only implement the named methods
      -- release the note instead of retriggering it at zero velocity.
      if m.vel == 0 then
        midi_out:note_off(m.note, 0, m.ch)
      else
        midi_out:note_on(m.note, m.vel, m.ch)
      end
    elseif t == "note_off" then
      midi_out:note_off(m.note, m.vel or 0, m.ch)
    elseif t == "cc" then
      midi_out:cc(m.cc, m.val, m.ch)
    elseif t == "pitchbend" then
      midi_out:pitchbend(m.val, m.ch)
    elseif t == "key_pressure" then
      midi_out:key_pressure(m.note, m.val, m.ch)
    elseif t == "channel_pressure" then
      midi_out:channel_pressure(m.val, m.ch)
    elseif t == "program_change" then
      midi_out:program_change(m.val, m.ch)
    else
      -- clock, sysex, anything to_msg does not decode: pass the bytes through
      midi_out:send(data)
    end
  end
  last_out = util.time()
  local msg = midi.to_msg(data)
  if msg.ch then
    if msg.type == "note_on" and msg.vel > 0 then
      notes_on[msg.ch] = notes_on[msg.ch] or {}
      notes_on[msg.ch][msg.note] = true
    elseif msg.type == "note_off" or (msg.type == "note_on" and msg.vel == 0) then
      if notes_on[msg.ch] then notes_on[msg.ch][msg.note] = nil end
    end
  end
end

local function all_notes_off()
  for ch, notes in pairs(notes_on) do
    for note, _ in pairs(notes) do
      if midi_out then midi_out:note_off(note, 0, ch) end
    end
  end
  notes_on = {}
end

-- transport -----------------------------------------------------------

local function stop()
  if play_clock then
    clock.cancel(play_clock)
    play_clock = nil
  end
  if state == "rec" then
    len = util.time() - rec_start
    dirty = #events > 0
  end
  all_notes_off()
  state = "stop"
end

local function start_rec()
  stop()
  events = {}
  len = 0
  play_pos = 0
  rec_start = util.time()
  state = "rec"
end

local function seek(pos)
  play_pos = util.clamp(pos, 0, len)
  play_idx = 1
  while play_idx <= #events and events[play_idx].t < play_pos do
    play_idx = play_idx + 1
  end
end

local function start_play()
  if #events == 0 then return end
  stop()
  if play_pos >= len then play_pos = 0 end
  seek(play_pos)
  state = "play"
  play_clock = clock.run(function()
    local t0 = util.time() - play_pos
    while true do
      clock.sleep(1 / 200)
      play_pos = util.time() - t0
      while play_idx <= #events and events[play_idx].t <= play_pos do
        send(events[play_idx].data)
        play_idx = play_idx + 1
      end
      if play_pos >= len then
        if params:get("loop") == 2 then
          all_notes_off()
          play_pos = 0
          play_idx = 1
          t0 = util.time()
        else
          play_pos = len
          all_notes_off()
          state = "stop"
          play_clock = nil
          return
        end
      end
    end
  end)
end

-- files ---------------------------------------------------------------

local function save_take()
  if #events == 0 then return end
  local name = next_take_name()
  local ok, err = recfile.write(DATA_DIR .. name, events, len)
  if ok then
    dirty = false
    scan_takes()
    for i, v in ipairs(takes) do
      if v == name then take_sel = i end
    end
    print("midirec: saved " .. name)
  else
    print("midirec: save failed - " .. tostring(err))
  end
end

local function load_take(i)
  if not takes[i] then return end
  stop()
  local e, l = recfile.read(DATA_DIR .. takes[i])
  if e then
    events = e
    len = l
    play_pos = 0
    play_idx = 1
    dirty = false
    print("midirec: loaded " .. takes[i] .. " (" .. #events .. " events)")
  else
    print("midirec: load failed - " .. tostring(l))
  end
end

-- midi input ----------------------------------------------------------

local function midi_event(data)
  local echo
  if state == "rec" then
    echo = params:get("echo_rec") == 2
  elseif state == "stop" then
    echo = params:get("echo_standby") == 2
  elseif state == "play" then
    echo = params:get("echo_play") == 2
  else
    echo = false
  end
  if echo then send(data) end
  if state == "rec" then
    local t = util.time() - rec_start
    local copy = {}
    for i = 1, #data do copy[i] = data[i] end
    events[#events + 1] = {t = t, data = copy}
    len = t
  end
end

-- lifecycle -----------------------------------------------------------

function init()
  util.make_dir(DATA_DIR)
  scan_takes()

  params:add_separator("midirec")

  local names = {}
  for i = 1, 16 do
    names[i] = midi.vports[i].name ~= "none"
      and (i .. ": " .. midi.vports[i].name) or (i .. ": -")
  end

  params:add_option("in_port", "in port", names, 1)
  params:set_action("in_port", function(v)
    if midi_in then midi_in.event = nil end
    midi_in = midi.connect(v)
    midi_in.event = midi_event
  end)

  params:add_option("out_port", "out port", names, 1)
  params:set_action("out_port", function(v)
    all_notes_off()
    midi_out = midi.connect(v)
  end)

  params:add_option("loop", "loop", {"off", "on"}, 1)

  params:add_option("echo_rec", "echo rec", {"off", "on"}, 2)
  params:add_option("echo_standby", "echo standby", {"off", "on"}, 2)
  -- default off: playing along shares the notes_on table with playback, so
  -- a note still held when the take ends or loops gets released by the
  -- panic in all_notes_off(). see the comment there.
  params:add_option("echo_play", "echo play", {"off", "on"}, 1)

  params:add_trigger("save", "save take")
  params:set_action("save", function() save_take() end)

  params:bang()

  screen_metro = metro.init(function()
    if norns.menu.status() == false then redraw() end
  end, 1 / 15)
  screen_metro:start()
end

function cleanup()
  stop()
  if screen_metro then screen_metro:stop() end
  if midi_in then midi_in.event = nil end
end

-- ui ------------------------------------------------------------------

function key(n, z)
  if z == 0 then return end
  if n == 2 then
    if state == "play" then
      stop()
    elseif state == "rec" then
      stop()
      save_take()
    else
      start_play()
    end
  elseif n == 3 then
    if state == "rec" then
      stop()
      save_take()
    else
      start_rec()
    end
  end
  redraw()
end

function enc(n, d)
  if n == 1 then
    if #takes > 0 then
      local new = util.clamp(take_sel + d, 1, #takes)
      if new ~= take_sel then
        take_sel = new
        load_take(take_sel)
      end
    end
  elseif n == 2 then
    if state ~= "rec" and len > 0 then
      seek(play_pos + d * (len / 100))
    end
  elseif n == 3 then
    if d ~= 0 then
      params:set("loop", d > 0 and 2 or 1)
    end
  end
  redraw()
end

function redraw()
  screen.clear()

  -- title
  screen.level(4)
  screen.move(0, 8)
  screen.text("midirec")

  -- take name
  screen.level(#takes > 0 and 15 or 3)
  screen.move(128, 8)
  screen.text_right(takes[take_sel] and takes[take_sel]:gsub("%.mrec$", "")
    or "-")

  -- transport
  screen.level(15)
  screen.move(0, 30)
  if state == "rec" then
    screen.text("● REC")
  elseif state == "play" then
    screen.text("▶ PLAY")
    -- out activity: bright on send, fades over ~150ms
    local age = util.time() - last_out
    local lvl = age < 0.05 and 15 or age < 0.10 and 10 or age < 0.15 and 5 or 0
    screen.level(2)
    screen.rect(40.5, 23.5, 6, 6)
    screen.stroke()
    if lvl > 0 then
      screen.level(lvl)
      screen.rect(41, 24, 5, 5)
      screen.fill()
    end
    screen.level(15)
  else
    screen.text("■ STOP")
  end

  -- time
  screen.move(128, 30)
  if state == "rec" then
    screen.text_right(fmt_time(util.time() - rec_start))
  else
    screen.text_right(fmt_time(play_pos) .. " / " .. fmt_time(len))
  end

  -- position bar
  screen.level(3)
  screen.rect(0.5, 38.5, 127, 5)
  screen.stroke()
  if len > 0 then
    screen.level(state == "rec" and 15 or 10)
    local w = (state == "rec" and 1 or util.clamp(play_pos / len, 0, 1)) * 125
    screen.rect(1.5, 39.5, math.max(1, w), 3)
    screen.fill()
  end

  -- bottom row: event count left, loop state right.
  -- the 128px row only fits two items in the default font (~5px/char),
  -- so no key hints here -- they are in the header comment, which norns
  -- shows in the SELECT menu.
  screen.level(4)
  screen.move(0, 54)
  screen.text(#events .. " ev" .. (dirty and " *" or ""))

  local looping = params:get("loop") == 2
  screen.level(looping and 15 or 3)
  screen.move(128, 54)
  screen.text_right(looping and "LOOP" or "loop")

  screen.update()
end
