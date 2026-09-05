-- recfile: read/write midirec take files
--
-- format 2: plain text, one line per event, times in beats
--   line 1: "midirec 2"
--   line 2: "len <beats>"
--   line 3: "tempo <bpm at record time>"   (informational)
--   line 4: "tsig 4 4"                      (informational, always 4/4 for now)
--   rest:   "<beats> <b1> <b2> <b3> ..."    (beats from take start)
--
-- format 1 (seconds) is not read. nothing outside this repo ever wrote it.

local recfile = {}

function recfile.write(path, events, len, tempo)
  local f, err = io.open(path, "w")
  if not f then return false, err end
  f:write("midirec 2\n")
  f:write(string.format("len %.6f\n", len or 0))
  f:write(string.format("tempo %.3f\n", tempo or 120))
  f:write("tsig 4 4\n")
  for i = 1, #events do
    local e = events[i]
    local parts = {string.format("%.6f", e.t)}
    for j = 1, #e.data do
      parts[#parts + 1] = tostring(e.data[j])
    end
    f:write(table.concat(parts, " "), "\n")
  end
  f:close()
  return true
end

-- returns events, len, tempo  or  nil, err
function recfile.read(path)
  local f, err = io.open(path, "r")
  if not f then return nil, err end

  local header = f:read("*l")
  if not header or not header:match("^midirec 2") then
    f:close()
    return nil, "not a midirec v2 file"
  end

  local events = {}
  local len = 0
  local tempo

  for line in f:lines() do
    local l = line:match("^len%s+([%d%.%-]+)")
    local tp = line:match("^tempo%s+([%d%.%-]+)")
    if l then
      len = tonumber(l) or 0
    elseif tp then
      tempo = tonumber(tp)
    elseif line:match("^tsig") then
      -- ignored for now
    elseif line ~= "" then
      local nums = {}
      for tok in line:gmatch("%S+") do
        nums[#nums + 1] = tonumber(tok)
      end
      if #nums >= 2 then
        local t = table.remove(nums, 1)
        events[#events + 1] = {t = t, data = nums}
      end
    end
  end
  f:close()

  if len <= 0 and #events > 0 then
    len = events[#events].t
  end
  return events, len, tempo
end

return recfile
