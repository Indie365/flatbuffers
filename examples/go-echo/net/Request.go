// Code generated by the FlatBuffers compiler. DO NOT EDIT.

package net

import (
	flatbuffers "github.com/google/flatbuffers/go"

	hero "echo/hero"
)

type RequestT struct {
	Player *hero.WarriorT `json:"player"`
}

func (t *RequestT) Pack(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	if t == nil { return 0 }
	playerOffset := t.Player.Pack(builder)
	RequestStart(builder)
	RequestAddPlayer(builder, playerOffset)
	return RequestEnd(builder)
}

func (rcv *Request) UnPackTo(t *RequestT) {
	t.Player = rcv.Player(nil).UnPack()
}

func (rcv *Request) UnPack() *RequestT {
	if rcv == nil { return nil }
	t := &RequestT{}
	rcv.UnPackTo(t)
	return t
}

type Request struct {
	_tab flatbuffers.Table
}

func GetRootAsRequest(buf []byte, offset flatbuffers.UOffsetT) *Request {
	n := flatbuffers.GetUOffsetT(buf[offset:])
	x := &Request{}
	x.Init(buf, n+offset)
	return x
}

func GetSizePrefixedRootAsRequest(buf []byte, offset flatbuffers.UOffsetT) *Request {
	n := flatbuffers.GetUOffsetT(buf[offset+flatbuffers.SizeUint32:])
	x := &Request{}
	x.Init(buf, n+offset+flatbuffers.SizeUint32)
	return x
}

func (rcv *Request) Init(buf []byte, i flatbuffers.UOffsetT) {
	rcv._tab.Bytes = buf
	rcv._tab.Pos = i
}

func (rcv *Request) Table() flatbuffers.Table {
	return rcv._tab
}

func (rcv *Request) Player(obj *hero.Warrior) *hero.Warrior {
	o := flatbuffers.UOffsetT(rcv._tab.Offset(4))
	if o != 0 {
		x := rcv._tab.Indirect(o + rcv._tab.Pos)
		if obj == nil {
			obj = new(hero.Warrior)
		}
		obj.Init(rcv._tab.Bytes, x)
		return obj
	}
	return nil
}

func RequestStart(builder *flatbuffers.Builder) {
	builder.StartObject(1)
}
func RequestAddPlayer(builder *flatbuffers.Builder, player flatbuffers.UOffsetT) {
	builder.PrependUOffsetTSlot(0, flatbuffers.UOffsetT(player), 0)
}
func RequestEnd(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	return builder.EndObject()
}
