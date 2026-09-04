-- recfile: read/write midirec take files
--
-- format: plain text, one line per event
--   line 1: "midirec 1"
--   line 2: "len <seconds>"
--   rest:   "<time> <b1> <b2> <b3> ..."   (time = seconds from start)

local recfile = {}

function recfile.write(path, events, len)
  local f, err = io.open(path, "w")
  if not f then return false, err end
  f:write("midirec 1\n")
  f:write(string.format("len %.6f\n", len or 0))
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

function recfile.read(path)
  local f, err = io.open(path, "r")
  if not f then return nil, err end

  local header = f:read("*l")
  if not header or not header:match("^midirec") then
    f:close()
    return nil, "not a midirec file"
  end

  local events = {}
  local len = 0

  for line in f:lines() do
    local l = line:match("^len%s+([%d%.%-]+)")
    if l then
      len = tonumber(l) or 0
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
  return events, len
end

return recfile
