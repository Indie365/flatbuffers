--[[ MyGame.InParentNamespace

  Automatically generated by the FlatBuffers compiler, do not modify.
  Or modify. I'm a message, not a cop.

  flatc version: 22.11.22

  Declared by  : //monster_test.fbs
  Rooting type : MyGame.Example.Monster (//monster_test.fbs)

--]]

local flatbuffers = require('flatbuffers')

local InParentNamespace = {}
local mt = {}

function InParentNamespace.New()
  local o = {}
  setmetatable(o, {__index = mt})
  return o
end

function mt:Init(buf, pos)
  self.view = flatbuffers.view.New(buf, pos)
end

function InParentNamespace.Start(builder)
  builder:StartObject(0)
end

function InParentNamespace.End(builder)
  return builder:EndObject()
end

return InParentNamespace