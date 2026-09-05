-- midirec
-- record + play midi
--
-- E1 select take
-- K2 play / stop
-- K3 record / stop
-- E2 scrub (not rec)
-- E3 loop on / off
-- grid: takes, or keyboard.
-- bottom row: scale oct- oct+ hold
--   ... stop rec loop menu
--
-- time is in beats from the norns
-- clock (PARAMETERS > CLOCK sets
-- source + tempo). 4/4 assumed.
--
-- play mode multi: grid presses
-- layer takes, press again to
-- stop one. single: one take,
-- next is queued for the bar.
--
-- params: in/out port, loop,
-- play mode single / multi,
-- rec on first note,
-- length / launch / play quantize,
-- follow transport,
-- echo rec / standby / play,
-- grid channel / velocity / base / scale

local recfile = include("midirec/lib/recfile")
local musicutil = require("musicutil")

local DATA_DIR = _path.data .. "midirec/"

local midi_in
local midi_out
local g              -- grid, if one is attached
local grid_mode = "takes" -- "takes" | "keys"
local keys_held = {}      -- [note] = number of grid cells holding it
local hold_on = false     -- keyboard hold: notes latch until pressed again
local flash_until = {}    -- [key] = time; momentary led feedback for taps
local FLASH = 0.15        -- seconds a tapped control key stays lit
local scale_down = false  -- scale key held; with a note press it sets the root
local scale_used = false  -- ...and if it did, releasing it does not step scales
-- keyboard base note, channel, velocity, scale are params
local SCALES = {
  "Chromatic", "Major", "Natural Minor", "Dorian", "Mixolydian", "Lydian",
  "Phrygian", "Harmonic Minor", "Major Pentatonic", "Minor Pentatonic",
  "Blues Scale", "Whole Tone",
}
local scale_notes = {}    -- note numbers of the current scale, from base
local scale_row = 5       -- scale degrees per row up the grid

local state = "stop" -- "stop" | "arm" | "rec" | "play"
-- "arm": record pressed with "rec on note" on. nothing is timed or stored
-- until the first note-on arrives; that note becomes t = 0.

-- all time is in beats on the norns global clock (clock.get_beats()), which
-- follows whatever source PARAMETERS > CLOCK selects: internal, midi in,
-- link, crow. so takes follow tempo changes and lock to an external clock
-- without any clock parsing here.
local BEATS_PER_BAR = 4   -- 4/4 assumed for now

-- the focused take: what the screen, E1/E2/K2 and save work on
local events = {}    -- raw {t = beats from take start, data = {bytes...}}
local len = 0        -- length in beats
local play_pos = 0   -- where K2 starts it from; mirrors its player while playing

-- every playing take is a player. play mode "multi" lets several run at
-- once, each on its own clock coroutine; "single" keeps one and swaps it
-- at the pass boundary via `queued`.
--   take     index in takes
--   events   raw copy read from disk; pe = play-quantized copy playback reads
--   len, pos, idx, t0 (global beat that maps to take beat 0)
--   clock    coroutine id; pending = waiting on launch quantize
local players = {}

local rec_start = 0  -- beat the current recording started (may be snapped)
local screen_metro

local takes = {}     -- list of filenames in DATA_DIR
local take_sel = 1
local dirty = false  -- unsaved recording
local rec_name       -- filename the current recording will save as
local loaded         -- index in takes of the take held in events, if any
local queued         -- take index to switch to when the current pass ends
local read_take      -- forward decls, defined under files
local load_file

-- held notes per source, [src][ch][note] = true. src is "echo" for live
-- input passed through, or a player table for that player's notes. tracked
-- separately so stopping or wrapping one take releases only its own notes.
local notes_on = {echo = {}}
local last_out = -1  -- util.time() of last outgoing message

-- helpers -------------------------------------------------------------

-- "bar.beat", 1-based, like a sequencer readout
local function fmt_pos(b)
  b = math.max(0, b)
  return string.format("%d.%d",
    math.floor(b / BEATS_PER_BAR) + 1, math.floor(b % BEATS_PER_BAR) + 1)
end

-- length in bars, decimals only when needed: "4b", "2.5b"
local function fmt_len(b)
  return string.format("%g", math.max(0, b) / BEATS_PER_BAR) .. "b"
end

-- quantize option (1 off, 2 beat, 3 bar) -> beats, or nil for off
local function quant(param)
  local v = params:get(param)
  if v == 2 then return 1 end
  if v == 3 then return BEATS_PER_BAR end
  return nil
end

local function round_to(b, q)
  if not q then return b end
  return math.floor(b / q + 0.5) * q
end

-- play quantize is applied on the way out, never to the stored take, so it
-- can be changed or turned off later. note-ons snap to the grid; each
-- note-off moves by the same offset as its note-on so durations survive.
-- cc, bend, pressure are left alone. a note pushed past the loop end wraps
-- to the start of the pass.
local PLAY_QUANT = {nil, 1, 1 / 2, 1 / 4, 1 / 8} -- off, 1/4, 1/8, 1/16, 1/32
local function derive(events, len)
  local q = PLAY_QUANT[params:get("play_quant")]
  local out = {}
  if not q or len <= 0 then
    for i, e in ipairs(events) do out[i] = e end
    return out
  end
  local shift = {} -- [ch*128+note] = offset applied to the pending note-on
  for i, e in ipairs(events) do
    local t = e.t
    local m = midi.to_msg(e.data)
    if m and m.ch then
      local k = m.ch * 128 + (m.note or 0)
      if m.type == "note_on" and m.vel > 0 then
        local qt = round_to(t, q)
        shift[k] = qt - t
        t = qt
      elseif m.type == "note_off" or (m.type == "note_on" and m.vel == 0) then
        if shift[k] then
          t = t + shift[k]
          shift[k] = nil
        end
      end
    end
    out[#out + 1] = {t = t % len, data = e.data, i = i}
  end
  -- table.sort is not stable: break ties on recorded order so a note-off
  -- and the next note-on of the same pitch at one grid point keep their order
  table.sort(out, function(a, b)
    if a.t == b.t then return a.i < b.i end
    return a.t < b.t
  end)
  return out
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
local function send(data, src)
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
    local held = notes_on[src]
    if not held then
      held = {}
      notes_on[src] = held
    end
    if msg.type == "note_on" and msg.vel > 0 then
      held[msg.ch] = held[msg.ch] or {}
      held[msg.ch][msg.note] = true
    elseif msg.type == "note_off" or (msg.type == "note_on" and msg.vel == 0) then
      if held[msg.ch] then held[msg.ch][msg.note] = nil end
    end
  end
end

-- release held notes for one source, or every source when src is nil
local function all_notes_off(src)
  local srcs = {}
  if src then
    srcs[1] = src
  else
    for k in pairs(notes_on) do srcs[#srcs + 1] = k end
  end
  for _, k in ipairs(srcs) do
    local held = notes_on[k]
    if held then
      for ch, notes in pairs(held) do
        for note, _ in pairs(notes) do
          if midi_out then midi_out:note_off(note, 0, ch) end
        end
      end
    end
    -- echo lives forever; a player's table goes when the player does
    notes_on[k] = k == "echo" and {} or nil
  end
end

-- transport -----------------------------------------------------------

-- state is "rec"/"arm" while recording, else follows the player list
local function update_state()
  if state == "rec" or state == "arm" then return end
  state = #players > 0 and "play" or "stop"
end

local function player_for(i)
  for _, p in ipairs(players) do
    if p.take == i then return p end
  end
end

local function any_pending()
  for _, p in ipairs(players) do
    if p.pending then return true end
  end
  return false
end

-- the player the screen follows: the focused take's if playing, else the
-- first one started
local function focus_player()
  return (loaded and player_for(loaded)) or players[1]
end

local function player_seek(p, pos)
  p.pos = util.clamp(pos, 0, p.len)
  p.idx = 1
  while p.idx <= #p.pe and p.pe[p.idx].t < p.pos do
    p.idx = p.idx + 1
  end
  p.t0 = clock.get_beats() - p.pos
end

local function player_remove(p)
  if p.clock then
    clock.cancel(p.clock)
    p.clock = nil
  end
  all_notes_off(p)
  for k, v in ipairs(players) do
    if v == p then
      table.remove(players, k)
      break
    end
  end
  update_state()
end

local function stop_players()
  while #players > 0 do player_remove(players[#players]) end
end

-- start take i from `pos` beats. immediate skips launch quantize (an
-- external transport start is already on the boundary). one player per
-- take: a take already playing is left alone.
local function player_start(i, pos, immediate)
  if player_for(i) then return end
  local e, l = load_file(i)
  if not e or #e == 0 or l <= 0 then return end
  local p = {take = i, events = e, len = l, pos = pos or 0, idx = 1, t0 = 0,
    pending = false}
  p.pe = derive(e, l)
  players[#players + 1] = p
  update_state()
  p.clock = clock.run(function()
    local q = (not immediate) and quant("launch_quant")
    if q then
      -- clock.sync waits for the next multiple of q on the global beat
      -- grid, so every take launches on the same grid
      p.pending = true
      clock.sync(q)
      p.pending = false
    end
    player_seek(p, p.pos)
    while true do
      clock.sleep(1 / 200)
      p.pos = clock.get_beats() - p.t0
      while p.idx <= #p.pe and p.pe[p.idx].t <= p.pos do
        send(p.pe[p.idx].data, p)
        p.idx = p.idx + 1
      end
      if p.pos >= p.len then
        -- wrap by advancing the origin by exactly len rather than resetting
        -- to "now", so the few ms this poll overshot do not accumulate and
        -- the take stays locked to the beat grid pass after pass
        if queued and p.take == loaded then
          -- single mode, E1 turned during play: swap takes here at the
          -- pass boundary, loop or not. an empty or unreadable take stops.
          local qi = queued
          queued = nil
          all_notes_off(p)
          local e2, l2 = load_file(qi)
          if e2 and #e2 > 0 and l2 > 0 then
            local old = p.len
            p.take, p.events, p.len = qi, e2, l2
            p.pe = derive(e2, l2)
            p.t0 = p.t0 + old
            p.pos = clock.get_beats() - p.t0
            p.idx = 1
            read_take(qi) -- focus follows
          else
            p.clock = nil
            player_remove(p)
            return
          end
        elseif params:get("loop") == 2 then
          all_notes_off(p)
          p.t0 = p.t0 + p.len
          p.pos = clock.get_beats() - p.t0
          p.idx = 1
        else
          p.clock = nil
          player_remove(p)
          return
        end
      end
    end
  end)
  return p
end

-- play quantize changed: re-derive every player in place, re-finding the
-- index from the current position so nothing double-fires
local function rebuild_players()
  for _, p in ipairs(players) do
    p.pe = derive(p.events, p.len)
    if not p.pending then player_seek(p, p.pos) end
  end
end

-- stop everything: all players, and the recording if one is running
local function stop()
  local pending = queued
  queued = nil
  stop_players()
  if state == "rec" then
    local raw = math.max(0, clock.get_beats() - rec_start)
    -- length quantize rounds to the nearest beat/bar, min one unit, so a
    -- stop pressed a hair late does not add a whole extra bar. events past
    -- the new end are the tail of that overshoot; drop them.
    local q = quant("len_quant")
    len = q and math.max(q, round_to(raw, q)) or raw
    if q then
      while #events > 0 and events[#events].t >= len do
        events[#events] = nil
      end
    end
    dirty = #events > 0
  elseif state == "arm" then
    len = 0
    dirty = false
  end
  state = "stop"
  -- stopped with a take queued: load it now so the header and events agree
  if pending then read_take(pending) end
end

local function start_rec()
  stop()
  events = {}
  len = 0
  play_pos = 0
  -- snap the start to the nearest launch-quantize boundary. pressed just
  -- after a downbeat the take starts on that downbeat; pressed just before,
  -- anything played early lands at t = 0.
  rec_start = round_to(clock.get_beats(), quant("launch_quant"))
  rec_name = next_take_name()
  loaded = nil
  state = params:get("rec_on_note") == 2 and "arm" or "rec"
end

-- move the focused take. while it plays, its player follows.
local function seek(pos)
  play_pos = util.clamp(pos, 0, len)
  local p = loaded and player_for(loaded)
  if p then player_seek(p, play_pos) end
end

-- K2 play: the focused take from play_pos
local function start_play(immediate)
  if not loaded or #events == 0 then return end
  if play_pos >= len then play_pos = 0 end
  player_start(loaded, play_pos, immediate)
end

-- files ---------------------------------------------------------------

local function save_take()
  if #events == 0 then return end
  local name = next_take_name()
  local ok, err = recfile.write(DATA_DIR .. name, events, len,
    clock.get_tempo())
  if ok then
    dirty = false
    scan_takes()
    for i, v in ipairs(takes) do
      if v == name then take_sel = i; loaded = i end
    end
    print("midirec: saved " .. name)
  else
    print("midirec: save failed - " .. tostring(err))
  end
end

-- read take i from disk. returns events, len  or nil.
load_file = function(i)
  if not takes[i] then return nil end
  local e, l = recfile.read(DATA_DIR .. takes[i])
  if not e then
    print("midirec: load failed - " .. tostring(l))
    return nil
  end
  return e, l
end

-- make take i the focused take without touching transport
read_take = function(i)
  local e, l = load_file(i)
  if not e then return false end
  events = e
  len = l
  play_pos = 0
  dirty = false
  loaded = i
  print("midirec: loaded " .. takes[i] .. " (" .. #events .. " events)")
  return true
end

local function load_take(i)
  if not takes[i] then return end
  stop()
  read_take(i)
end

-- E1 (and the grid in single mode). while recording it is ignored. while
-- playing: single mode queues the take for the pass boundary, picking the
-- playing take cancels the queue; multi mode just moves focus.
local function select_take(i)
  if not takes[i] then return end
  if state == "rec" or state == "arm" then return end
  take_sel = i
  if state == "play" then
    if params:get("play_mode") == 1 then
      queued = i ~= loaded and i or nil
    else
      read_take(i)
    end
  else
    load_take(i)
  end
end

-- transport buttons. K2/K3 on the device and the grid control row both
-- land here so they cannot drift apart.
local function k2_press()
  if state == "play" then
    stop()
  elseif state == "rec" or state == "arm" then
    stop()
    save_take()
  else
    start_play()
  end
end

local function k3_press()
  if state == "rec" or state == "arm" then
    stop()
    save_take()
  else
    start_rec()
  end
end

-- midi input ----------------------------------------------------------

-- store a message into the take if recording. the first note-on while
-- armed starts the clock; anything before it is dropped.
local function record(data)
  -- realtime bytes (clock ticks, start/stop, active sensing) never go in a
  -- take. a clock-sending input would otherwise fill it with 0xF8s that
  -- get re-sent on playback.
  if data[1] >= 0xF8 then return end
  if state == "arm" then
    local msg = midi.to_msg(data)
    if msg.type == "note_on" and msg.vel > 0 then
      -- the first note is t = 0. with launch quantize on, snap the start to
      -- the nearest beat so the take sits on the grid; the note itself lands
      -- at 0 if it was early, or a hair after 0 if late.
      local b = clock.get_beats()
      rec_start = quant("launch_quant") and round_to(b, 1) or b
      state = "rec"
    end
  end
  if state == "rec" then
    local t = math.max(0, clock.get_beats() - rec_start)
    local copy = {}
    for i = 1, #data do copy[i] = data[i] end
    events[#events + 1] = {t = t, data = copy}
    len = t
  end
end

local function midi_event(data)
  local echo
  if state == "rec" or state == "arm" then
    echo = params:get("echo_rec") == 2
  elseif state == "stop" then
    echo = params:get("echo_standby") == 2
  elseif state == "play" then
    echo = params:get("echo_play") == 2
  else
    echo = false
  end
  if echo then send(data, "echo") end
  record(data)
end

-- grid ----------------------------------------------------------------
--
-- bottom row is a control row in both modes, from the right:
--   [cols]   menu: toggle takes <-> keyboard. always lit.
--   [cols-1] loop on / off (E3)
--   [cols-2] record (K3)
--   [cols-3] stop / play (K2)
-- keyboard mode only, from the left:
--   [1] tap: next scale. hold + press a note: set root to that pitch
--   [2] octave down   [3] octave up   [4] hold (latch) on / off
-- rows above it: takes mode, one cell per take, left to right then down.
-- keyboard mode, notes in fourths: +1 per column, +5 per row going up,
-- lowest note bottom-left. notes always sound on the out port and are
-- recorded like midi input.

local function grid_dims()
  return g.cols or 16, g.rows or 8
end

-- rebuild the note table for the current base and scale. rows step by the
-- number of degrees closest to a fourth, so chromatic is the usual fourths
-- layout and a 7-note scale steps 3 degrees, a pentatonic 2.
local function build_scale()
  local name = SCALES[params:get("grid_scale")]
  local n = 12
  for _, sc in ipairs(musicutil.SCALES) do
    if sc.name == name then n = #sc.intervals - 1 end -- drop the octave
  end
  scale_row = math.max(1, math.floor(n * 5 / 12 + 0.5))
  local cols, rows = 16, 8
  if g then cols, rows = grid_dims() end
  local length = cols + (rows - 2) * scale_row
  local notes = musicutil.generate_scale_of_length(
    params:get("grid_base"), name, length) or {}
  scale_notes = {}
  for i, note in ipairs(notes) do
    if note <= 127 then scale_notes[i] = note end
  end
end

local function scale_label()
  local root = musicutil.note_num_to_name(params:get("grid_base"), true)
  return root .. " " .. SCALES[params:get("grid_scale")]:lower()
end

local function grid_pos(i)
  local cols = grid_dims()
  return (i - 1) % cols + 1, (i - 1) // cols + 1
end

-- may return nil past the top of the scale table
local function grid_note(x, y)
  local _, rows = grid_dims()
  return scale_notes[(x - 1) + ((rows - 1) - y) * scale_row + 1]
end

local function keys_send(note, on)
  local status = (on and 0x90 or 0x80) + params:get("grid_ch") - 1
  local data = {status, note, on and params:get("grid_vel") or 0}
  send(data, "echo")
  record(data)
end

-- several cells share a note in a fourths layout, so count holds per note
-- and only send when the count crosses zero
local function keys_press(note, z)
  if not note then return end
  local n = keys_held[note] or 0
  if hold_on then
    -- latch: press toggles, release does nothing
    if z ~= 1 then return end
    if n > 0 then
      keys_send(note, false)
      keys_held[note] = nil
    else
      keys_send(note, true)
      keys_held[note] = 1
    end
    return
  end
  if z == 1 then
    if n == 0 then keys_send(note, true) end
    keys_held[note] = n + 1
  elseif n > 0 then
    if n == 1 then keys_send(note, false) end
    keys_held[note] = n > 1 and n - 1 or nil
  end
end

local function keys_release()
  for note in pairs(keys_held) do keys_send(note, false) end
  keys_held = {}
end

-- move the keyboard root to the pitch class of `note`, staying in the
-- octave nearest the current base so the layout does not jump registers
local function set_root(note)
  local base = params:get("grid_base")
  local pc = note % 12
  local best, dist = base, 999
  for cand = pc, 127, 12 do
    local d = math.abs(cand - base)
    if d < dist then best, dist = cand, d end
  end
  params:set("grid_base", best)
end

-- light control key `k` for FLASH seconds so even a quick tap is visible
local function flash(k) flash_until[k] = util.time() + FLASH end
local function flashing(k) return (flash_until[k] or 0) > util.time() end

local function shift_octave(d)
  local b = params:get("grid_base") + d * 12
  if b >= 0 and b <= 127 then params:set("grid_base", b) end
end

local function grid_redraw()
  if not g or not g.device then return end
  local cols, rows = grid_dims()
  g:all(0)
  -- one time sample, fast rate exactly 2x slow, so every slow edge lands
  -- on a fast edge and the two never drift apart
  local t = util.time()
  local blink = math.floor(t * 4) % 2 == 0   -- queued: fast (2 Hz)
  local slow = math.floor(t * 2) % 2 == 0    -- playing: slow (1 Hz)
  if grid_mode == "takes" then
    for i = 1, math.min(#takes, cols * (rows - 1)) do
      local x, y = grid_pos(i)
      -- 8 is half bright on varibright and the lowest level a monobright
      -- grid shows as on, so one value covers both
      local lvl = 8
      local p = player_for(i)
      if i == queued then
        lvl = blink and 12 or 6
      elseif p then
        -- waiting on launch quantize: fast; playing: slow
        if p.pending then lvl = blink and 15 or 6 else lvl = slow and 15 or 6 end
      elseif i == loaded then
        lvl = 15
      end
      g:led(x, y, lvl)
    end
  else
    local root = params:get("grid_base") % 12
    for y = 1, rows - 1 do
      for x = 1, cols do
        local note = grid_note(x, y)
        if note then
          -- roots at 6: a hint on varibright, dark on monobright so the
          -- keyboard shows only held notes there
          local lvl = keys_held[note] and 15 or (note % 12 == root and 6 or 2)
          g:led(x, y, lvl)
        end
      end
    end
    -- keyboard controls: scale, oct-, oct+, hold. octave keys idle low
    -- (dark on monobright) and flash on a tap; hold is a toggle, off dark
    g:led(1, rows, scale_down and 15 or 8)
    g:led(2, rows, flashing("oct_down") and 15 or 4)
    g:led(3, rows, flashing("oct_up") and 15 or 4)
    g:led(4, rows, hold_on and 15 or 4)
  end
  -- control row. rec and stop idle at 8 so they read as buttons, full on
  -- when active
  g:led(cols, rows, 15)
  g:led(cols - 2, rows,
    state == "rec" and 15 or (state == "arm" and (blink and 15 or 8)) or 8)
  g:led(cols - 3, rows, state == "play" and 15 or 8)
  -- loop key: shows on/off in takes mode. on the keyboard page it stays
  -- dark and only flashes on a tap, so the row reads as controls, not state
  if grid_mode == "keys" then
    g:led(cols - 1, rows, flashing("loop") and 15 or 0)
  else
    g:led(cols - 1, rows, params:get("loop") == 2 and 15 or 4)
  end
  g:refresh()
end

local function grid_key(x, y, z)
  local cols, rows = grid_dims()
  if y == rows then
    local keys = grid_mode == "keys"
    -- momentary keyboard controls need the release too
    if keys and x == 1 then
      if z == 1 then
        scale_down, scale_used = true, false
      else
        scale_down = false
        -- a plain tap steps the scale; a hold used to set the root does not
        if not scale_used then
          params:set("grid_scale", params:get("grid_scale") % #SCALES + 1)
        end
      end
      return
    elseif keys and x == 2 then
      if z == 1 then flash("oct_down"); shift_octave(-1) end
      return
    elseif keys and x == 3 then
      if z == 1 then flash("oct_up"); shift_octave(1) end
      return
    end
    if z ~= 1 then return end
    if keys and x == 4 then
      hold_on = not hold_on
      if not hold_on then keys_release() end
    elseif x == cols - 1 then
      flash("loop")
      params:set("loop", params:get("loop") == 2 and 1 or 2)
    elseif x == cols then
      if grid_mode == "keys" then
        keys_release()
        hold_on = false
        grid_mode = "takes"
      else
        grid_mode = "keys"
      end
    elseif x == cols - 2 then
      k3_press()
    elseif x == cols - 3 then
      k2_press()
    end
    redraw()
    return
  end
  if grid_mode == "keys" then
    local note = grid_note(x, y)
    if scale_down then
      -- scale key held: this press picks the root instead of playing
      if z == 1 and note then
        scale_used = true
        set_root(note)
      end
      return
    end
    keys_press(note, z)
    return
  end
  if z ~= 1 then return end
  local i = (y - 1) * cols + x
  if not takes[i] then return end
  if state == "rec" or state == "arm" then return end
  if params:get("play_mode") == 2 then
    -- multi: each press toggles that take. launch quantize applies, so
    -- with it on new takes fall in on the grid; off, they run free and
    -- phase against whatever else is going. focus follows the press.
    local p = player_for(i)
    if p then
      player_remove(p)
    else
      read_take(i)
      take_sel = i
      player_start(i, 0)
    end
  elseif state == "stop" then
    -- single, from stop: a grid press is "play this one"
    load_take(i)
    take_sel = i
    start_play()
  else
    select_take(i)
  end
  redraw()
end

-- lifecycle -----------------------------------------------------------

function init()
  util.make_dir(DATA_DIR)
  scan_takes()
  -- the header shows take_sel from the start, so K2 / the grid play key
  -- must have it loaded too
  if #takes > 0 then read_take(take_sel) end

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
  -- single: one take plays, E1/grid queue the next for the pass boundary.
  -- multi: grid presses layer takes, any number at once.
  params:add_option("play_mode", "play mode", {"single", "multi"}, 2)
  params:set_action("play_mode", function(v)
    if v == 1 and #players > 1 then stop() end
  end)
  params:add_option("rec_on_note", "rec on first note", {"off", "on"}, 1)

  params:add_separator("time")
  local QUANT = {"off", "beat", "bar"}
  params:add_option("len_quant", "length quantize", QUANT, 3)
  params:add_option("launch_quant", "launch quantize", QUANT, 3)
  params:add_option("play_quant", "play quantize",
    {"off", "1/4", "1/8", "1/16", "1/32"}, 1)
  -- re-derive the playback table in place. mid-pass the index is re-found
  -- from the current position so nothing double-fires.
  params:set_action("play_quant", function() rebuild_players() end)
  -- with an external clock source, its start plays the loaded take from 0
  -- and its stop stops playback
  params:add_option("follow", "follow transport", {"off", "on"}, 2)

  params:add_separator("grid keyboard")
  params:add_number("grid_ch", "grid channel", 1, 16, 1)
  params:add_number("grid_vel", "grid velocity", 1, 127, 100)
  params:add_number("grid_base", "grid base note", 0, 127, 36,
    function(p) return musicutil.note_num_to_name(p:get(), true) end)
  -- a base note change while keys are held would send note-offs for the
  -- wrong pitches, so release first
  params:add_option("grid_scale", "grid scale", SCALES, 1)
  params:set_action("grid_base", function() keys_release(); build_scale() end)
  params:set_action("grid_scale", function() keys_release(); build_scale() end)
  params:set_action("grid_ch", function() keys_release() end)

  params:add_option("echo_rec", "echo rec", {"off", "on"}, 2)
  params:add_option("echo_standby", "echo standby", {"off", "on"}, 2)
  params:add_option("echo_play", "echo play", {"off", "on"}, 2)

  params:add_trigger("save", "save take")
  params:set_action("save", function() save_take() end)

  params:bang()

  -- external transport (midi / link start & stop). norns resets its beat
  -- count on start, so playing from 0 right now is on the grid already.
  clock.transport.start = function()
    if params:get("follow") == 2 and state == "stop" and loaded then
      play_pos = 0
      start_play(true)
    end
  end
  clock.transport.stop = function()
    if params:get("follow") == 2 and state == "play" then stop() end
  end

  g = grid.connect()
  g.key = grid_key
  build_scale()

  screen_metro = metro.init(function()
    if norns.menu.status() == false then redraw() end
    grid_redraw()
  end, 1 / 15)
  screen_metro:start()
end

function cleanup()
  stop()
  all_notes_off()
  clock.transport.start = nil
  clock.transport.stop = nil
  if screen_metro then screen_metro:stop() end
  if g then
    g.key = nil
    keys_release()
    if g.device then g:all(0); g:refresh() end
  end
  if midi_in then midi_in.event = nil end
end

-- ui ------------------------------------------------------------------

function key(n, z)
  if z == 0 then return end
  if n == 2 then
    k2_press()
  elseif n == 3 then
    k3_press()
  end
  redraw()
end

function enc(n, d)
  if n == 1 then
    if #takes > 0 then
      local new = util.clamp(take_sel + d, 1, #takes)
      if new ~= take_sel then select_take(new) end
    end
  elseif n == 2 then
    if state ~= "rec" and state ~= "arm" and len > 0 then
      local p = loaded and player_for(loaded)
      seek((p and p.pos or play_pos) + d) -- one beat per click
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

  -- row 2: grid keyboard scale left, tempo + clock source right
  screen.level(4)
  screen.move(0, 18)
  screen.text(scale_label())
  screen.move(128, 18)
  -- %d needs an integer in lua 5.3; a float here blanks the whole screen
  screen.text_right(string.format("%d %s", math.floor(clock.get_tempo() + 0.5),
    params:string("clock_source")))

  -- take name. while recording, show the take this will be saved as, so
  -- the header does not lag behind until the recording stops.
  local shown = (state == "rec" or state == "arm") and rec_name
    or takes[take_sel]
  screen.level(shown and 15 or 3)
  screen.move(128, 8)
  shown = shown and shown:gsub("%.mrec$", "") or "-"
  screen.text_right(queued and ("next: " .. shown) or shown)

  -- transport
  screen.level(15)
  screen.move(0, 30)
  if state == "rec" then
    screen.text("● REC")
  elseif state == "arm" then
    -- waiting for the first note. blink so it reads as live, not stuck.
    screen.level(math.floor(util.time() * 2) % 2 == 0 and 15 or 6)
    screen.text("● ARM")
    screen.level(15)
  elseif state == "play" and any_pending() then
    screen.level(math.floor(util.time() * 4) % 2 == 0 and 15 or 6)
    screen.text("▶ WAIT")
    screen.level(15)
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

  -- time: the focused take's player if it is playing, else the first
  -- player, else the focused take at rest
  local fp = focus_player()
  local pos, plen = play_pos, len
  if fp then pos, plen = fp.pos, fp.len end
  screen.move(128, 30)
  if state == "rec" then
    screen.text_right(fmt_pos(clock.get_beats() - rec_start))
  elseif state == "arm" then
    screen.text_right(fmt_pos(0))
  else
    screen.text_right(fmt_pos(pos) .. " / " .. fmt_len(plen))
  end

  -- position bar
  screen.level(3)
  screen.rect(0.5, 38.5, 127, 5)
  screen.stroke()
  if plen > 0 then
    screen.level(state == "rec" and 15 or 10)
    local w = (state == "rec" and 1 or util.clamp(pos / plen, 0, 1)) * 125
    screen.rect(1.5, 39.5, math.max(1, w), 3)
    screen.fill()
  end

  -- bottom row: event count left, loop state right.
  -- the 128px row only fits two items in the default font (~5px/char),
  -- so no key hints here -- they are in the header comment, which norns
  -- shows in the SELECT menu.
  screen.level(4)
  screen.move(0, 54)
  local info = #events .. " ev" .. (dirty and " *" or "")
  if #players > 1 then info = info .. "  " .. #players .. " playing" end
  screen.text(info)

  local looping = params:get("loop") == 2
  screen.level(looping and 15 or 3)
  screen.move(128, 54)
  screen.text_right(looping and "LOOP" or "loop")

  screen.update()
end
