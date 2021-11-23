/*
 * Copyright 2021 Google Inc. All rights reserved.
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

#ifndef FLATBUFFERS_BFBS_GEN_H_
#define FLATBUFFERS_BFBS_GEN_H_

#include <cstdint>

#include "flatbuffers/bfbs_generator.h"
#include "flatbuffers/reflection_generated.h"

namespace flatbuffers {

void ForAllEnums(
    const flatbuffers::Vector<flatbuffers::Offset<reflection::Enum>> *enums,
    std::function<void(const reflection::Enum *)> func) {
  for (auto it = enums->cbegin(); it != enums->cend(); ++it) { func(*it); }
}

void ForAllObjects(
    const flatbuffers::Vector<flatbuffers::Offset<reflection::Object>> *objects,
    std::function<void(const reflection::Object *)> func) {
  for (auto it = objects->cbegin(); it != objects->cend(); ++it) { func(*it); }
}

void ForAllEnumValues(const reflection::Enum *enum_def,
                      std::function<void(const reflection::EnumVal *)> func) {
  for (auto it = enum_def->values()->cbegin(); it != enum_def->values()->cend();
       ++it) {
    func(*it);
  }
}

void ForAllDocumentation(
    const flatbuffers::Vector<flatbuffers::Offset<flatbuffers::String>>
        *documentation,
    std::function<void(const flatbuffers::String *)> func) {
  if (!documentation) { return; }
  for (auto it = documentation->cbegin(); it != documentation->cend(); ++it) {
    func(*it);
  }
}

// Maps the field index into object->fields() to the field's ID (the ith element
// in the return vector).
static std::vector<uint32_t> FieldIdToIndex(const reflection::Object *object) {
  std::vector<uint32_t> field_index_by_id;
  field_index_by_id.resize(object->fields()->size());

  // Create the mapping of field ID to the index into the vector.
  for (uint32_t i = 0; i < object->fields()->size(); ++i) {
    auto field = object->fields()->Get(i);
    field_index_by_id[field->id()] = i;
  }

  return field_index_by_id;
}

static bool IsStructOrTable(const reflection::BaseType base_type) {
  return base_type == reflection::Obj;
}

static bool IsScalar(const reflection::BaseType base_type) {
  return base_type >= reflection::UType && base_type <= reflection::Double;
}

static bool IsFloatingPoint(const reflection::BaseType base_type) {
  return base_type == reflection::Float || base_type == reflection::Double;
}

static bool IsBool(const reflection::BaseType base_type) {
  return base_type == reflection::Bool;
}

static bool IsSingleByte(const reflection::BaseType base_type) {
  return base_type >= reflection::UType && base_type <= reflection::UByte;
}

static bool IsVector(const reflection::BaseType base_type) {
  return base_type == reflection::Vector;
}

static std::string MakeCamelCase(const std::string &in,
                                 bool uppercase_first = true) {
  std::string s;
  for (size_t i = 0; i < in.length(); i++) {
    if (!i && uppercase_first)
      s += static_cast<char>(::toupper(static_cast<unsigned char>(in[0])));
    else if (in[i] == '_' && i + 1 < in.length())
      s += static_cast<char>(::toupper(static_cast<unsigned char>(in[++i])));
    else
      s += in[i];
  }
  return s;
}

static std::string Denamespace(const flatbuffers::String *name,
                               std::string &ns) {
  const size_t pos = name->str().find_last_of('.');
  if (pos == std::string::npos) {
    ns = "";
    return name->str();
  }
  ns = name->str().substr(0, pos);
  return name->str().substr(pos + 1);
}

static std::string Denamespace(const flatbuffers::String *name) {
  std::string ns;
  return Denamespace(name, ns);
}

// A concrete base Flatbuffer Generator that specific language generators can
// derive from.
class BaseBfbsGenerator : public BfbsGenerator {
 public:
  virtual ~BaseBfbsGenerator() {}
  BaseBfbsGenerator() : schema_(nullptr) {}

  virtual GeneratorStatus GenerateFromSchema(
      const reflection::Schema *schema) = 0;

  //
  virtual uint64_t SupportedAdvancedFeatures() const = 0;

  // Override of the Generator::generate method that does the initial
  // deserialization and verification steps.
  GeneratorStatus Generate(const uint8_t *buffer,
                           int64_t length) FLATBUFFERS_OVERRIDE {
    flatbuffers::Verifier verifier(buffer, static_cast<size_t>(length));
    if (!reflection::VerifySchemaBuffer(verifier)) {
      return FAILED_VERIFICATION;
    }

    // Store the root schema since there are cases where leaf nodes refer to
    // things in the root schema (e.g., indexing the objects).
    schema_ = reflection::GetSchema(buffer);

    const uint64_t advance_features = schema_->advanced_features();
    if (advance_features > SupportedAdvancedFeatures()) {
      return FAILED_VERIFICATION;
    }

    GeneratorStatus status = GenerateFromSchema(schema_);
    schema_ = nullptr;
    return status;
  }

 protected:
  const reflection::Object *GetObject(const reflection::Type *type) const {
    if (type->index() >= 0 && IsStructOrTable(type->base_type())) {
      return GetObjectByIndex(type->index());
    }
    return nullptr;
  }

  const reflection::Enum *GetEnum(const reflection::Type *type) const {
    // TODO(derekbailey): it would be better to have a explicit list of allowed
    // base types, instead of negating Obj types.
    if (type->index() >= 0 && !IsStructOrTable(type->base_type())) {
      return GetEnumByIndex(type->index());
    }
    return nullptr;
  }

  // Used to get a object that is reference by index. (e.g.
  // reflection::Type::index). Returns nullptr if no object is available.
  const reflection::Object *GetObjectByIndex(int32_t index) const {
    if (!schema_ || index < 0 ||
        index >= static_cast<int32_t>(schema_->objects()->size())) {
      return nullptr;
    }
    return schema_->objects()->Get(index);
  }

  // Used to get a enum that is reference by index. (e.g.
  // reflection::Type::index). Returns nullptr if no enum is available.
  const reflection::Enum *GetEnumByIndex(int32_t index) const {
    if (!schema_ || index < 0 ||
        index >= static_cast<int32_t>(schema_->enums()->size())) {
      return nullptr;
    }
    return schema_->enums()->Get(index);
  }

  void ForAllFields(const reflection::Object *object,
                    std::function<void(const reflection::Field *)> func,
                    bool backwards = false) const {
    const std::vector<uint32_t> field_to_id_map = FieldIdToIndex(object);
    for (size_t i = 0; i < field_to_id_map.size(); ++i) {
      func(object->fields()->Get(
          field_to_id_map[backwards ? field_to_id_map.size() - (i + 1) : i]));
    }
  }

  bool IsTable(const reflection::Type *type, bool use_element = false) const {
    return !IsStruct(type, use_element);
  }

  bool IsStruct(const reflection::Type *type, bool use_element = false) const {
    const reflection::BaseType base_type =
        use_element ? type->element() : type->base_type();
    return IsStructOrTable(base_type) &&
           GetObjectByIndex(type->index())->is_struct();
  }

  const reflection::Schema *schema_;
};

}  // namespace flatbuffers

#endif  // FLATBUFFERS_BFBS_GEN_H_