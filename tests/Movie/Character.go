// Code generated by the FlatBuffers compiler. DO NOT EDIT.

package Movie

import (
	"strconv"

	flatbuffers "github.com/google/flatbuffers/go"
)

type Character byte

const (
	CharacterNONE     Character = 0
	CharacterMuLan    Character = 1
	CharacterRapunzel Character = 2
	CharacterBelle    Character = 3
	CharacterBookFan  Character = 4
	CharacterOther    Character = 5
	CharacterUnused   Character = 6

	CharacterVerifyValueMin Character = 0
	CharacterVerifyValueMax Character = 6
)

var EnumNamesCharacter = map[Character]string{
	CharacterNONE:     "NONE",
	CharacterMuLan:    "MuLan",
	CharacterRapunzel: "Rapunzel",
	CharacterBelle:    "Belle",
	CharacterBookFan:  "BookFan",
	CharacterOther:    "Other",
	CharacterUnused:   "Unused",
}

var EnumValuesCharacter = map[string]Character{
	"NONE":     CharacterNONE,
	"MuLan":    CharacterMuLan,
	"Rapunzel": CharacterRapunzel,
	"Belle":    CharacterBelle,
	"BookFan":  CharacterBookFan,
	"Other":    CharacterOther,
	"Unused":   CharacterUnused,
}

func (v Character) String() string {
	if s, ok := EnumNamesCharacter[v]; ok {
		return s
	}
	return "Character(" + strconv.FormatInt(int64(v), 10) + ")"
}

type CharacterT struct {
	Type  Character
	Value interface{}
}

func (t *CharacterT) Pack(builder *flatbuffers.Builder) flatbuffers.UOffsetT {
	if t == nil {
		return 0
	}
	switch t.Type {
	case CharacterMuLan:
		return t.Value.(*AttackerT).Pack(builder)
	case CharacterRapunzel:
		return t.Value.(*RapunzelT).Pack(builder)
	case CharacterBelle:
		return t.Value.(*BookReaderT).Pack(builder)
	case CharacterBookFan:
		return t.Value.(*BookReaderT).Pack(builder)
	case CharacterOther:
		return  builder.CreateString(t.Value.(string))
	case CharacterUnused:
		return  builder.CreateString(t.Value.(string))
	}
	return 0
}

// UnPack use for single union field
func (rcv Character) UnPack(table flatbuffers.Table) *CharacterT {
	switch rcv {
	case CharacterMuLan:
		x := GetTableAsAttacker(&table)
		return &CharacterT{Type: CharacterMuLan, Value: x.UnPack()}
	case CharacterRapunzel:
		x := GetStructAsRapunzel(&table)
		return &CharacterT{Type: CharacterRapunzel, Value: x.UnPack()}
	case CharacterBelle:
		x := GetStructAsBookReader(&table)
		return &CharacterT{Type: CharacterBelle, Value: x.UnPack()}
	case CharacterBookFan:
		x := GetStructAsBookReader(&table)
		return &CharacterT{Type: CharacterBookFan, Value: x.UnPack()}
	case CharacterOther:
		x :=  string(table.StringsVector(table.Pos))
		return &CharacterT{Type: CharacterOther, Value: x }
	case CharacterUnused:
		x :=  string(table.StringsVector(table.Pos))
		return &CharacterT{Type: CharacterUnused, Value: x }
	}
	return nil
}

// UnPackVector use for vector of unions
func (rcv Character) UnPackVector(table flatbuffers.Table) *CharacterT {
	switch rcv {
	case CharacterMuLan:
		x := GetTableVectorAsAttacker(&table)
		return &CharacterT{Type: CharacterMuLan, Value: x.UnPack()}
	case CharacterRapunzel:
		x := GetStructVectorAsRapunzel(&table)
		return &CharacterT{Type: CharacterRapunzel, Value: x.UnPack()}
	case CharacterBelle:
		x := GetStructVectorAsBookReader(&table)
		return &CharacterT{Type: CharacterBelle, Value: x.UnPack()}
	case CharacterBookFan:
		x := GetStructVectorAsBookReader(&table)
		return &CharacterT{Type: CharacterBookFan, Value: x.UnPack()}
	case CharacterOther:
		x :=  string(table.ByteVector(table.Pos))
		return &CharacterT{Type: CharacterOther, Value: x }
	case CharacterUnused:
		x :=  string(table.ByteVector(table.Pos))
		return &CharacterT{Type: CharacterUnused, Value: x }
	}
	return nil
}
