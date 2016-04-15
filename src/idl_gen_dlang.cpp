/*
 * Copyright 2014 Google Inc. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// independent from idl_parser, since this code is not needed for most clients

#include <list>
#include <algorithm>

#include "flatbuffers/flatbuffers.h"
#include "flatbuffers/idl.h"
#include "flatbuffers/util.h"

namespace flatbuffers {

namespace dlang {

static std::string GenGetter(const Type &type);
static std::string GenMethod( const Type &type);

static std::string GenTypeBasic(const Type &type);
static std::string GenTypeGet(const Type &type);

static std::string FunctionStart(char upper) {
    return std::string() + static_cast<char>(tolower(upper));
}

static std::string GenTypeBasic(const Type &type) {
    static const char *gtypename[] = {
    #define FLATBUFFERS_TD(ENUM, IDLTYPE, CTYPE, JTYPE, GTYPE, NTYPE, PTYPE, DTYPE) \
    #DTYPE,
        FLATBUFFERS_GEN_TYPES(FLATBUFFERS_TD)
    #undef FLATBUFFERS_TD
    };

    return gtypename[type.base_type];
}

static void GenComment(const std::vector<std::string> &dc, std::string *code_ptr, const char *prefix = "") {
    if (dc.begin() == dc.end()) {
        // Don't output empty comment blocks with 0 lines of comment content.
        return;
    }

    std::string &code = *code_ptr;

    std::string line_prefix = std::string(prefix) + "///";
    for (auto it = dc.begin();
         it != dc.end();
         ++it) {
        code += line_prefix + *it + "\n";
    }
}



static std::string GenTypePointer(const Type &type) {
    switch (type.base_type) {
    case BASE_TYPE_STRING:
        return "string";
    case BASE_TYPE_VECTOR:
        return GenTypeGet(type.VectorType());
    case BASE_TYPE_STRUCT:
        return type.struct_def->name;
    case BASE_TYPE_UNION:
        // fall through
        return "T";
    default:
        return "T";
    }
}

static std::string GenTypeGet(const Type &type) {
    return IsScalar(type.base_type)
            ? GenTypeBasic(type)
            : GenTypePointer(type);
}


static std::string GenDefaultValue(const Value &value) {
    return value.type.base_type == BASE_TYPE_BOOL
            ? (value.constant == "0" ? "false" : "true")
            : value.constant;
}

static void GenEnum( EnumDef &enum_def,
                     std::string *code_ptr) {
    std::string &code = *code_ptr;
    if (enum_def.generated) return;
    //printf("!generated %s\n", enum_def.name.c_str());

    // Generate enum definitions of the form:
    // public static (final) int name = value;
    // In Java, we use ints rather than the Enum feature, because we want them
    // to map directly to how they're used in C/C++ and file formats.
    // That, and Java Enums are expensive, and not universally liked.
    GenComment(enum_def.doc_comment, code_ptr);

    code += std::string("")  + "enum " + enum_def.name;

    code += " : " + GenTypeBasic( enum_def.underlying_type);

    code += "\n{\n";

    for (auto it = enum_def.vals.vec.begin();
         it != enum_def.vals.vec.end();
         ++it) {
        auto &ev = **it;
        GenComment(ev.doc_comment, code_ptr, "  ");

        code += "  ";

        if ( ev.name != "NONE")
            code += " " + FunctionStart(ev.name[0]) + ev.name.substr(1) + " = ";
        else
            code += " " + ev.name + " = ";
        code += NumToString(ev.value);
        code += ",\n";
    }

    // Close the class
    code += std::string("") + "}" + "\n\n";
}

// Returns the function name that is able to read a value of the given type.
static std::string GenGetter( const Type &type) {
    switch (type.base_type) {
    case BASE_TYPE_STRING: return "__string";
    case BASE_TYPE_STRUCT: return "__struct";
    case BASE_TYPE_UNION:  return "__union!";
    case BASE_TYPE_VECTOR: return GenGetter(type.VectorType());
    default: {
        std::string getter = "_buffer." + FunctionStart( 'G') + "et!";
        if (type.base_type == BASE_TYPE_BOOL) {
            getter += "ubyte";
        } else {
            getter += GenTypeGet(type);
        }
        return getter;
    }
    }
}

// Returns the method name for use with add/put calls.
static std::string GenMethod( const Type &type) {
    return IsScalar(type.base_type)
            ? MakeCamel(GenTypeBasic( type))
            : (IsStruct(type) ? "Struct" : "Offset");
}

// Recursively generate arguments for a constructor, to deal with nested
// structs.
static void GenStructArgs(const StructDef &struct_def,
                          std::string *code_ptr, const char *nameprefix) {
    std::string &code = *code_ptr;
    for (auto it = struct_def.fields.vec.begin();
         it != struct_def.fields.vec.end();
         ++it) {
        auto &field = **it;
        if (IsStruct(field.value.type)) {
            // Generate arguments for a struct inside a struct. To ensure names
            // don't clash, and to make it obvious these arguments are constructing
            // a nested struct, prefix the name with the struct name.
            GenStructArgs( *field.value.type.struct_def, code_ptr,
                           (field.value.type.struct_def->name + "_").c_str());
        } else {
            code += ", ";
            code += GenTypeBasic(field.value.type);

            code += " ";
            code += nameprefix;
            code += MakeCamel(field.name, false);
        }
    }
}

// Recusively generate struct construction statements of the form:
// builder.put!type(name);
// and insert manual padding.
static void GenStructBody(const StructDef &struct_def,
                          std::string *code_ptr, const char *nameprefix) {
    std::string &code = *code_ptr;
    code += "    builder." + FunctionStart( 'P') + "rep(";
    code += NumToString(struct_def.minalign) + ", ";
    code += NumToString(struct_def.bytesize) + ");\n";
    for (auto it = struct_def.fields.vec.rbegin();
         it != struct_def.fields.vec.rend(); ++it) {
        auto &field = **it;
        if (field.padding) {
            code += "    builder." + FunctionStart( 'P') + "ad(";
            code += NumToString(field.padding) + ");\n";
        }
        if (IsStruct(field.value.type)) {
            GenStructBody( *field.value.type.struct_def, code_ptr,
                           (field.value.type.struct_def->name + "_").c_str());
        } else {
            code += "    builder." + FunctionStart( 'P') + "ut!";
            code += GenTypeBasic(field.value.type) + "(";
            code +=  nameprefix + MakeCamel(field.name, false);
            code += ");\n";
        }
    }
}

static void GenStruct(const Parser &parser,
                      StructDef &struct_def, std::string *code_ptr) {
    if (struct_def.generated) return;
    std::string &code = *code_ptr;

    // Create imports for modules that this struct depends on.
    std::string namespace_general;
    auto &namespaces = parser.namespaces_.back()->components;
    for (auto it = namespaces.begin(); it != namespaces.end(); ++it) {
        namespace_general += FunctionStart( (*it)[0]) + (*it).substr(1);
        if (namespace_general.length()) {
            namespace_general += ".";
        }
    }
    std::list<std::string> imports;
    for (auto it = struct_def.fields.vec.begin();
         it != struct_def.fields.vec.end();
         ++it) {
        auto &field = **it;
        if (field.deprecated) continue;

        if (field.value.type.struct_def)
            imports.push_back(field.value.type.struct_def->name);
        if (field.value.type.enum_def)
            imports.push_back(field.value.type.enum_def->name);
    }
    imports.unique();
    for (auto it = imports.begin(); it != imports.end(); ++it) {
        auto import = "import " + namespace_general + FunctionStart( (*it)[0]) + (*it).substr(1) + ";\n";
        transform (import.begin(),import.end(), import.begin(), tolower);
        code += import;
    }
    if (imports.size())
        code += "\n";


    GenComment(struct_def.doc_comment, code_ptr);

    code += "struct " + struct_def.name;

    code += " {\n";
    //Dlang mixin Struct
    code += std::string("  mixin ") + (struct_def.fixed? "Struct" : "Table") + "!" + struct_def.name + ";\n\n";

    if (!struct_def.fixed) {
        // Generate a special accessor for the table that when used as the root
        // of a FlatBuffer
        std::string method_name = FunctionStart( 'G') + "etRootAs" + struct_def.name;
        // create convenience method that doesn't require an existing object
        code += std::string("  ")  + "static " + struct_def.name + " " + method_name + "(ByteBuffer _bb) ";
        code += "{  return " + struct_def.name + ".init_(_bb.get!int(_bb.position()) + _bb.position(), _bb); }\n";

        if (parser.root_struct_def_ == &struct_def) {
            if (parser.file_identifier_.length()) {
                // Check if a buffer has the identifier.
                code += std::string("  ")  + "static ";
                code += "bool" + struct_def.name;
                code += "BufferHasIdentifier(ByteBuffer _bb) { return ";
                code += "__has_identifier(_bb, \"" + parser.file_identifier_;
                code += "\"); }\n";
            }
        }
    }

    for (auto it = struct_def.fields.vec.begin();
         it != struct_def.fields.vec.end();
         ++it) {
        auto &field = **it;
        if (field.deprecated) continue;
        GenComment(field.doc_comment, code_ptr, "  ");
        std::string type_name = GenTypeGet(field.value.type);
        std::string type_name_dest = GenTypeGet(field.value.type);
        std::string method_start = std::string("  ") + type_name_dest + " ";


        if (field.value.type.base_type == BASE_TYPE_VECTOR) {
              method_start = std::string("  ") + "auto " + MakeCamel(field.name, false);
              code += method_start + "() { ";
              code += "return Iterator!(";
              code += struct_def.name + ", " + type_name +", \"" + field.name;
              code += "\")(this); }\n";
        }

        std::string nullValue = "null";
        bool typeNeedsExtraHandling = false;

        typeNeedsExtraHandling = !IsScalar(field.value.type.base_type) && !IsScalar(field.value.type.element);
        method_start = std::string("  ") + (typeNeedsExtraHandling? "Nullable!" : "") +
                (field.value.type.base_type==BASE_TYPE_UNION? "T" : type_name) + " " +
                MakeCamel(field.name, false);
        nullValue = "Nullable!" + (field.value.type.base_type==BASE_TYPE_UNION? "T" : type_name) + ".init";

        // Most field accessors need to retrieve and test the field offset first,
        // this is the prefix code for that:
        auto offset_prefix = " { int o = __offset(" +
                NumToString(field.value.offset) +
                "); return o != 0 ? " +
                (typeNeedsExtraHandling
                 ? "Nullable!" + (field.value.type.base_type==BASE_TYPE_UNION? "T" : type_name) + "("
                 : "");

        std::string getter =  GenGetter(field.value.type);

        // Most field accessors need to retrieve and test the field offset first,
        // this is the prefix code for that:
        if (IsScalar(field.value.type.base_type)) {
            method_start = std::string("  @property ") + method_start;
            code += method_start;
            code += "()";
            if (struct_def.fixed) {
                code += " { return " + getter;
                code += "(_pos + " + NumToString(field.value.offset) + ")";
            } else {
                code += offset_prefix + getter;
                code += "(o + _pos)";
                code +=  " : ";
                code += GenDefaultValue(field.value);
            }
        } else {
            switch (field.value.type.base_type) {
            case BASE_TYPE_STRUCT:
                 method_start = std::string("  @property ") + method_start;
                 code += method_start;
                code += "(";
                if (struct_def.fixed) {
                    code += ") { return Nullable!" + type_name + "(" + type_name + "init_(_pos + ";

                    code += NumToString(field.value.offset) + ", _buffer)";
                    code += ")";
                } else {
                    code += ")";
                    code += offset_prefix;
                    code += type_name;
                    code += ".init_(";
                    code += field.value.type.struct_def->fixed
                            ? "o + _pos"
                            : "__indirect(o + _pos)";
                    code += ", _buffer)) : " + nullValue;
                }
                break;
            case BASE_TYPE_STRING:
                method_start = std::string("  @property ") + method_start;
                code += method_start;
                code += "()";
                code += offset_prefix + getter + "(o + _pos)";
                code += ") : Nullable!" + type_name + ".init";
                break;
            case BASE_TYPE_VECTOR: {
                method_start = std::string("  ") + method_start;
                code += method_start;
                auto vectortype = field.value.type.VectorType();
                code += "(int j)";
                   code += offset_prefix ;
                if(IsScalar(field.value.type.element)){ //基本类型
                    code += getter;
                    code += "(__dvector(o) + j * " + NumToString(InlineSize(vectortype));
                    code +=  ") : ";
                    code += GenDefaultValue(field.value);
                } else if(field.value.type.element == BASE_TYPE_STRING ){ //string 类型处理
                    code += getter;
                    code += "(__dvector(o) + j * " + NumToString(InlineSize(vectortype));
                    code += ")) : Nullable!" + type_name + ".init";
                } else { //结构体和table处理，现在不支持union 和 vector的vector
                    code += type_name ;
                    code +=".init_(";
                    auto index = "__dvector(o) + j * " + NumToString(InlineSize(vectortype));
                    if (vectortype.base_type == BASE_TYPE_STRUCT) {
                        code += vectortype.struct_def->fixed ? index : std::string("__indirect(") + index + ")";
                        code += ", _buffer";
                    } else {
                        code += index;
                    }
                    code += std::string(")") + (typeNeedsExtraHandling? ")" : "")   + " : ";
                    code += IsScalar(field.value.type.element) ?  "0" : nullValue;
                }
                break;
            }
            case BASE_TYPE_UNION:
                method_start = std::string("  ") + method_start;
                code += method_start;
                code += "(T)()" + offset_prefix + getter;
                code += "(T)(o)";
                code += ")";
                code += " : " + nullValue;
                break;
            default:
                assert(0);
            }
        }
        code += "; ";
        code += "}\n";
        if (field.value.type.base_type == BASE_TYPE_VECTOR) {
            code += std::string("  @property ") + "int " + MakeCamel(field.name, false);
            code += "Length";
            code += "()";
            auto offset_prefix1 = " { int o = __offset(" +
                    NumToString(field.value.offset) +
                    "); return o != 0 ? ";
            code += offset_prefix1;
            code += "__vector_len(o)";
            code += " : 0; ";
            code += "}\n";
        }
    }
    code += "\n";
    if (struct_def.fixed) {
        // create a struct constructor function
        code += std::string("  ")  + "static int " + FunctionStart( 'C') + "reate";
        code += struct_def.name + "(FlatBufferBuilder builder";
        GenStructArgs( struct_def, code_ptr, "");
        code += ") {\n";
        GenStructBody( struct_def, code_ptr, "");
        code += "    return builder.";
        code += "offset()";
        code += ";\n  }\n";
    } else {
        // Generate a method that creates a table in one go. This is only possible
        // when the table has no struct fields, since those have to be created
        // inline, and there's no way to do so in Java.
        bool has_no_struct_fields = true;
        int num_fields = 0;
        for (auto it = struct_def.fields.vec.begin();
             it != struct_def.fields.vec.end(); ++it) {
            auto &field = **it;
            if (field.deprecated) continue;
            if (IsStruct(field.value.type)) {
                has_no_struct_fields = false;
            } else {
                num_fields++;
            }
        }
        if (has_no_struct_fields && num_fields) {
            // Generate a table constructor of the form:
            // public static void createName(FlatBufferBuilder builder, args...)
            code += std::string("  ")  + "static int " + FunctionStart( 'C') + "reate";
            code += struct_def.name;
            code += "(FlatBufferBuilder builder";
            for (auto it = struct_def.fields.vec.begin();
                 it != struct_def.fields.vec.end(); ++it) {
                auto &field = **it;
                if (field.deprecated) continue;
                code += ",\n      ";
                code += GenTypeBasic(field.value.type);
                code += " ";
                code += field.name;
            }
            code += ") {\n    builder.";
            code += FunctionStart( 'S') + "tartObject(";
            code += NumToString(struct_def.fields.vec.size()) + ");\n";
            for (size_t size = struct_def.sortbysize ? sizeof(largest_scalar_t) : 1;
                 size;
                 size /= 2) {
                for (auto it = struct_def.fields.vec.rbegin();
                     it != struct_def.fields.vec.rend(); ++it) {
                    auto &field = **it;
                    if (!field.deprecated &&
                            (!struct_def.sortbysize ||
                             size == SizeOf(field.value.type.base_type))) {
                        code += "    " + struct_def.name + ".";
                        code += FunctionStart( 'A') + "dd";
                        code += MakeCamel(field.name) + "(builder, " + field.name + ");\n";
                    }
                }
            }
            code += "    return " + struct_def.name + ".";
            code += FunctionStart( 'E') + "nd" + struct_def.name;
            code += "(builder);\n  }\n\n";
        }
        // Generate a set of static methods that allow table construction,
        // of the form:
        // public static void addName(FlatBufferBuilder builder, short name)
        // { builder.addShort(id, name, default); }
        // Unlike the Create function, these always work.
        code += std::string("  ")  + "static void " + FunctionStart( 'S') + "tart";
        code += struct_def.name;
        code += "(FlatBufferBuilder builder) { builder.";
        code += FunctionStart( 'S') + "tartObject(";
        code += NumToString(struct_def.fields.vec.size()) + "); }\n";
        for (auto it = struct_def.fields.vec.begin();
             it != struct_def.fields.vec.end(); ++it) {
            auto &field = **it;
            if (field.deprecated) continue;
            code += std::string("  ")  + "static void " + FunctionStart( 'A') + "dd";
            code += MakeCamel(field.name);
            code += "(FlatBufferBuilder builder, ";
            code += GenTypeBasic(field.value.type);
            auto argname = MakeCamel(field.name, false);
            if (!IsScalar(field.value.type.base_type)) argname += "Offset";
            code += " " + argname + ") { builder." + FunctionStart( 'A') + "dd";
            code += GenMethod( field.value.type) + "(";
            code += NumToString(it - struct_def.fields.vec.begin()) + ", ";
            code += argname;
            code += ", " + GenDefaultValue(field.value);
            code += "); }\n";
            if (field.value.type.base_type == BASE_TYPE_VECTOR) {
                auto vector_type = field.value.type.VectorType();
                auto alignment = InlineAlignment(vector_type);
                auto elem_size = InlineSize(vector_type);
                if (!IsStruct(vector_type)) {
                    // Generate a method to create a vector from a Java array.
                    code += std::string("  ")  + "static int " + FunctionStart( 'C') + "reate";
                    code += MakeCamel(field.name);
                    code += "Vector(FlatBufferBuilder builder, ";
                    code += GenTypeBasic(vector_type) + "[] data) ";
                    code += "{ builder." + FunctionStart( 'S') + "tartVector(";
                    code += NumToString(elem_size) + ", ";
                    code += std::string("") + "cast(int)" + "data." + FunctionStart( 'L') + "ength, ";
                    code += NumToString(alignment);
                    code += "); for (int i = ";
                    code += std::string("") + "cast(int)" + "data." + FunctionStart( 'L') + "ength - 1; i >= 0; i--) builder.";
                    code += FunctionStart( 'A') + "dd";
                    code += GenMethod( vector_type);
                    code += "(data[i]); return builder.";
                    code += FunctionStart( 'E') + "ndVector(); }\n";
                }
                // Generate a method to start a vector, data to be added manually after.
                code += std::string("  ")  + "static void " + FunctionStart( 'S') + "tart";
                code += MakeCamel(field.name);
                code += "Vector(FlatBufferBuilder builder, int numElems) ";
                code += "{ builder." + FunctionStart( 'S') + "tartVector(";
                code += NumToString(elem_size);
                code += ", numElems, " + NumToString(alignment);
                code += "); }\n";
            }
        }
        code += std::string("  ")  + "static int ";
        code += FunctionStart( 'E') + "nd" + struct_def.name;
        code += "(FlatBufferBuilder builder) {\n    int o = builder.";
        code += FunctionStart( 'E') + "ndObject();\n";
        for (auto it = struct_def.fields.vec.begin();
             it != struct_def.fields.vec.end();
             ++it) {
            auto &field = **it;
            if (!field.deprecated && field.required) {
                code += "    builder." + FunctionStart( 'R') + "equired(o, ";
                code += NumToString(field.value.offset);
                code += ");  // " + field.name + "\n";
            }
        }
        code += "    return o;\n  }\n";
        if (parser.root_struct_def_ == &struct_def) {
            code += std::string("  ")  + "static void ";
            code += FunctionStart( 'F') + "inish" + struct_def.name;
            code += "Buffer(FlatBufferBuilder builder, int offset) { ";
            code += "builder." + FunctionStart( 'F') + "inish(offset";
            if (parser.file_identifier_.length())
                code += ", \"" + parser.file_identifier_ + "\"";
            code += "); }\n";
        }
    }
    code += std::string("") + "}" + "\n\n";
}

// Save out the generated code for a single class while adding
// declaration boilerplate.
static bool SaveClass( const Parser &parser,
                       const Definition &def, const std::string &classcode,
                       const std::string &path, bool needs_includes) {
    if (!classcode.length()) return true;

    std::string unit_name = def.name;

    unit_name = FunctionStart(unit_name[0]) + unit_name.substr(1);


    std::string namespace_general;
    std::string namespace_dir = path;  // Either empty or ends in separator.
    auto &namespaces = parser.namespaces_.back()->components;
    for (auto it = namespaces.begin(); it != namespaces.end(); ++it) {
        namespace_general += FunctionStart( (*it)[0]) + (*it).substr(1);
        namespace_dir += FunctionStart( (*it)[0]) + (*it).substr(1) + kPathSeparator;
        if (namespace_general.length()) {
            namespace_general += ".";
        }
    }

    transform (namespace_dir.begin(),namespace_dir.end(), namespace_dir.begin(), tolower);
    //printf("namespace_dir: %s\n", namespace_dir.c_str());
    EnsureDirExists(namespace_dir);
    namespace_general += unit_name;

    //printf("namespace_general: %s\n", namespace_general.c_str());

    std::string code = "// automatically generated, do not modify\n\n";
    auto module = "module " + namespace_general + ";";
    transform (module.begin(),module.end(), module.begin(), tolower);
    code += module;
    code += "\n\n";
    if (needs_includes) code += "import google.flatbuffers;\n\n";
    code += classcode;
    auto filename = namespace_dir + unit_name + ".d";
    transform (filename.begin(),filename.end(), filename.begin(), tolower);
    return SaveFile(filename.c_str(), code, false);
}

static bool SavePackage(const Parser &parser,
                        const std::string &path, bool needs_includes) {
    std::string unit_name = "package";

    std::string namespace_general;
    std::string namespace_dir = path;  // Either empty or ends in separator.
    auto &namespaces = parser.namespaces_.back()->components;
    for (auto it = namespaces.begin(); it != namespaces.end(); ++it) {
        if (it != namespaces.end()-1) {
            namespace_general += FunctionStart( (*it)[0]) + (*it).substr(1);
        }
        namespace_dir += FunctionStart( (*it)[0]) + (*it).substr(1) + kPathSeparator;
        if (namespace_general.length() && it != namespaces.end()-1) {
            namespace_general += ".";
        }
    }
    transform (namespace_dir.begin(),namespace_dir.end(), namespace_dir.begin(), tolower);
    EnsureDirExists(namespace_dir);
    namespace_general += FunctionStart( (*(namespaces.end()-1))[0]) + (*(namespaces.end()-1)).substr(1);
    transform (namespace_general.begin(),namespace_general.end(), namespace_general.begin(), tolower);
    std::string code = "// automatically generated, do not modify\n\n";
    code += "module " + namespace_general + ";";
    code += "\n\n";
    if (needs_includes) code += std::string("public ") + "import google.flatbuffers;\n\n";
    std::list<std::string> modules;
    for (auto it = parser.enums_.vec.begin();
         it != parser.enums_.vec.end(); ++it) {
        modules.push_back((**it).name);
    }
    for (auto it = parser.structs_.vec.begin();
         it != parser.structs_.vec.end(); ++it) {
        modules.push_back((**it).name);
    }
    modules.unique();
    for (auto it = modules.begin();
         it != modules.end(); ++it) {
        auto import = "public import " + namespace_general + "." + FunctionStart( (*it)[0]) + (*it).substr(1) + ";\n";
        transform (import.begin(),import.end(), import.begin(), tolower);
        code += import;
    }
    auto filename = namespace_dir + unit_name + ".d";
    transform (filename.begin(),filename.end(), filename.begin(), tolower);
    return SaveFile(filename.c_str(), code, false);
}

}

bool GenerateDlang(const Parser &parser,
                   const std::string &path,
                   const std::string & /*file_name*/) {

    for (auto it = parser.enums_.vec.begin();
         it != parser.enums_.vec.end(); ++it) {
        //printf("enum: %s, %s\n", (*it)->name.c_str(), (*it)->file.c_str());
        std::string enumcode;
        dlang::GenEnum( **it, &enumcode);
        //printf("enumcode: %s\n", enumcode.c_str());
        if (!dlang::SaveClass( parser, **it, enumcode, path, false))
            return false;
    }

    for (auto it = parser.structs_.vec.begin();
         it != parser.structs_.vec.end(); ++it) {
        std::string declcode;
        dlang::GenStruct( parser, **it, &declcode);
        if (!dlang::SaveClass( parser, **it, declcode, path, true))
            return false;
    }

    if (parser.namespaces_.back()->components.size()) {
        if (!dlang::SavePackage(parser, path, true))
            return false;
    }

    return true;
}


}  // namespace flatbuffers
