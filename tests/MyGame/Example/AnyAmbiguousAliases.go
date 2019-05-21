// Code generated by the FlatBuffers compiler. DO NOT EDIT.

package Example

import "strconv"

type AnyAmbiguousAliasesT interface{}
type AnyAmbiguousAliases byte

const (
	AnyAmbiguousAliasesNONE AnyAmbiguousAliases = 0
	AnyAmbiguousAliasesM1   AnyAmbiguousAliases = 1
	AnyAmbiguousAliasesM2   AnyAmbiguousAliases = 2
	AnyAmbiguousAliasesM3   AnyAmbiguousAliases = 3
)

var EnumNamesAnyAmbiguousAliases = map[AnyAmbiguousAliases]string{
	AnyAmbiguousAliasesNONE: "NONE",
	AnyAmbiguousAliasesM1:   "M1",
	AnyAmbiguousAliasesM2:   "M2",
	AnyAmbiguousAliasesM3:   "M3",
}

var EnumValuesAnyAmbiguousAliases = map[string]AnyAmbiguousAliases{
	"NONE": AnyAmbiguousAliasesNONE,
	"M1":   AnyAmbiguousAliasesM1,
	"M2":   AnyAmbiguousAliasesM2,
	"M3":   AnyAmbiguousAliasesM3,
}

func (v AnyAmbiguousAliases) String() string {
	if s, ok := EnumNamesAnyAmbiguousAliases[v]; ok {
		return s
	}
	return "AnyAmbiguousAliases(" + strconv.FormatInt(int64(v), 10) + ")"
}
