/*
 * Copyright 2018 Google Inc. All rights reserved.
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

mod reflection_generated;
mod r#struct;
pub use crate::r#struct::Struct;
pub use crate::reflection_generated::reflection;

use flatbuffers::{Follow, ForwardsUOffset, Table};
use reflection_generated::reflection::{BaseType, Field, Object, Schema};

use core::mem::size_of;
use escape_string::escape;
use num::traits::float::Float;
use num::traits::int::PrimInt;
use num::traits::FromPrimitive;

/// Gets the root table from a trusted Flatbuffer.
///
/// # Safety
///
/// Flatbuffers accessors do not perform validation checks before accessing. Users
/// must trust `data` contains a valid flatbuffer. Reading unchecked buffers may cause panics or even UB.
pub unsafe fn get_any_root<'buf>(data: &[u8]) -> Table {
    <ForwardsUOffset<Table>>::follow(data, 0)
}

/// Gets an integer table field given its exact type. Returns default integer value if the field is not set. Returns None if the type size doesn't match.
///
/// # Safety
///
/// The value of the corresponding slot must have type T
pub unsafe fn get_field_integer<'a, T: Follow<'a, Inner = T> + PrimInt + FromPrimitive + 'a>(
    table: &'a Table,
    field: &Field,
) -> Option<T> {
    if size_of::<T>() != get_type_size(field.type_().base_type()) {
        return None;
    }

    let default = T::from_i64(field.default_integer());
    table.get::<T>(field.offset(), default)
}

/// Gets a floating point table field given its exact type. Returns default float value if the field is not set. Returns None if the type doesn't match.
///
/// # Safety
///
/// The value of the corresponding slot must have type T
pub unsafe fn get_field_float<'a, T: Follow<'a, Inner = T> + Float + 'a>(
    table: &'a Table,
    field: &Field,
) -> Option<T> {
    if core::mem::size_of::<T>() != get_type_size(field.type_().base_type()) {
        return None;
    }

    let default = T::from(field.default_real());
    table.get::<T>(field.offset(), default)
}

/// Gets a String table field given its exact type. Returns empty string if the field is not set. Returns None if the type doesn't match.
///
/// # Safety
///
/// The value of the corresponding slot must have type String
pub unsafe fn get_field_string<'a>(table: &'a Table, field: &Field) -> Option<&'a str> {
    if field.type_().base_type() != BaseType::String {
        return None;
    }

    table.get::<ForwardsUOffset<&'a str>>(field.offset(), Some(""))
}

/// Gets a `Struct` table field given its exact type. Returns [None] if the field is not set or the type doesn't match.
///
/// # Safety
///
/// The value of the corresponding slot must have type Struct
pub unsafe fn get_field_struct<'a>(table: &'a Table, field: &Field) -> Option<Struct<'a>> {
    // TODO inherited from C++: This does NOT check if the field is a table or struct, but we'd need
    // access to the schema to check the is_struct flag.
    if field.type_().base_type() != BaseType::Obj {
        return None;
    }

    table.get::<Struct>(field.offset(), None)
}

/// Gets a `Struct` struct field given its exact type.
///
/// # Safety
///
/// The value of the corresponding slot must have type Struct.
pub unsafe fn get_field_struct_in_struct<'a>(st: &'a Struct, field: &Field) -> Option<Struct<'a>> {
    // TODO inherited from C++: This does NOT check if the field is a table or struct, but we'd need
    // access to the schema to check the is_struct flag.
    if field.type_().base_type() != BaseType::Obj {
        return None;
    }

    st.get::<Struct>(field.offset() as usize)
}

/// Returns the value of any table field as a 64-bit int, regardless of what type it is. Returns default integer if the field is not set or None if the value cannot be parsed as integer.
///
/// # Safety
///
/// The field must point to valid value in the buffer if set.
pub unsafe fn get_any_field_integer(table: &Table, field: &Field) -> Option<i64> {
    if let Some(field_loc) = get_field_loc(table, field) {
        get_any_value_integer(field.type_().base_type(), table.buf(), field_loc)
    } else {
        Some(field.default_integer())
    }
}

/// Returns the value of any table field as a 64-bit floating point, regardless of what type it is. Returns default float if the field is not set or [None] if the value cannot be parsed as float.
///
/// # Safety
///
/// The field must point to valid value in the buffer if set.
pub unsafe fn get_any_field_float(table: &Table, field: &Field) -> Option<f64> {
    if let Some(field_loc) = get_field_loc(table, field) {
        get_any_value_float(field.type_().base_type(), table.buf(), field_loc)
    } else {
        Some(field.default_real())
    }
}

/// Returns the value of any table field as a string, regardless of what type it is. Returns empty string if the field is not set.
///
/// # Safety
///
/// The field must point to valid value in the buffer if set.
pub unsafe fn get_any_field_string(table: &Table, field: &Field, schema: &Schema) -> String {
    if let Some(field_loc) = get_field_loc(table, field) {
        get_any_value_string(
            field.type_().base_type(),
            table.buf(),
            field_loc,
            schema,
            field.type_().index() as usize,
        )
    } else {
        String::from("")
    }
}

/// Returns the value of any struct field as a 64-bit int, regardless of what type it is. Returns [None] if the value cannot be parsed as integer.
///
/// # Safety
///
/// The field must point to valid value in the buffer.
pub unsafe fn get_any_field_integer_in_struct(st: &Struct, field: &Field) -> Option<i64> {
    let field_loc = st.loc() + field.offset() as usize;

    get_any_value_integer(field.type_().base_type(), st.buf(), field_loc)
}

/// Returns the value of any struct field as a 64-bit floating point, regardless of what type it is. Returns [None] if the value cannot be parsed as float.
///
/// # Safety
///
/// The field must point to valid value in the buffer.
pub unsafe fn get_any_field_float_in_struct(st: &Struct, field: &Field) -> Option<f64> {
    let field_loc = st.loc() + field.offset() as usize;

    get_any_value_float(field.type_().base_type(), st.buf(), field_loc)
}

/// Returns the value of any struct field as a string, regardless of what type it is.
///
/// # Safety
///
/// The field must point to valid value in the buffer.
pub unsafe fn get_any_field_string_in_struct(
    st: &Struct,
    field: &Field,
    schema: &Schema,
) -> String {
    let field_loc = st.loc() + field.offset() as usize;

    get_any_value_string(
        field.type_().base_type(),
        st.buf(),
        field_loc,
        schema,
        field.type_().index() as usize,
    )
}

/// Returns the size of a scalar type in the `BaseType` enum. In the case of structs, returns the size of their offset (`UOffsetT`) in the buffer.
fn get_type_size(base_type: BaseType) -> usize {
    match base_type {
        BaseType::UType | BaseType::Bool | BaseType::Byte | BaseType::UByte => 1,
        BaseType::Short | BaseType::UShort => 2,
        BaseType::Int
        | BaseType::UInt
        | BaseType::Float
        | BaseType::String
        | BaseType::Vector
        | BaseType::Obj
        | BaseType::Union => 4,
        BaseType::Long | BaseType::ULong | BaseType::Double | BaseType::Vector64 => 8,
        _ => 0,
    }
}

/// Returns the absolute field location in the buffer and [None] if the field is not populated.
pub fn get_field_loc(table: &Table, field: &Field) -> Option<usize> {
    let field_offset = table.vtable().get(field.offset()) as usize;
    if field_offset == 0 {
        return None;
    }

    Some(table.loc() + field_offset)
}

/// Reads value as a 64-bit int from the provided byte slice at the specified location. Returns [None] if the value cannot be parsed as integer.
///
/// # Safety
///
/// Caller must ensure `buf.len() >= loc + size_of::<T>()` at all the access layers.
unsafe fn get_any_value_integer<'a>(base_type: BaseType, buf: &'a [u8], loc: usize) -> Option<i64> {
    match base_type {
        BaseType::UType | BaseType::UByte => i64::from_u8(u8::follow(buf, loc)),
        BaseType::Bool => bool::follow(buf, loc).try_into().ok(),
        BaseType::Byte => i64::from_i8(i8::follow(buf, loc)),
        BaseType::Short => i64::from_i16(i16::follow(buf, loc)),
        BaseType::UShort => i64::from_u16(u16::follow(buf, loc)),
        BaseType::Int => i64::from_i32(i32::follow(buf, loc)),
        BaseType::UInt => i64::from_u32(u32::follow(buf, loc)),
        BaseType::Long => Some(i64::follow(buf, loc)),
        BaseType::ULong => i64::from_u64(u64::follow(buf, loc)),
        BaseType::Float => i64::from_f32(f32::follow(buf, loc)),
        BaseType::Double => i64::from_f64(f64::follow(buf, loc)),
        BaseType::String => ForwardsUOffset::<&str>::follow(buf, loc)
            .parse::<i64>()
            .ok(),
        _ => None, // Tables & vectors do not make sense.
    }
}

/// Reads value as a 64-bit floating point from the provided byte slice at the specified location. Returns None if the value cannot be parsed as float.
///
/// # Safety
///
/// Caller must ensure `buf.len() >= loc + size_of::<T>()` at all the access layers.
unsafe fn get_any_value_float<'a>(base_type: BaseType, buf: &'a [u8], loc: usize) -> Option<f64> {
    match base_type {
        BaseType::UType | BaseType::UByte => f64::from_u8(u8::follow(buf, loc)),
        BaseType::Bool => bool::follow(buf, loc).try_into().ok(),
        BaseType::Byte => f64::from_i8(i8::follow(buf, loc)),
        BaseType::Short => f64::from_i16(i16::follow(buf, loc)),
        BaseType::UShort => f64::from_u16(u16::follow(buf, loc)),
        BaseType::Int => f64::from_i32(i32::follow(buf, loc)),
        BaseType::UInt => f64::from_u32(u32::follow(buf, loc)),
        BaseType::Long => f64::from_i64(i64::follow(buf, loc)),
        BaseType::ULong => f64::from_u64(u64::follow(buf, loc)),
        BaseType::Float => f64::from_f32(f32::follow(buf, loc)),
        BaseType::Double => Some(f64::follow(buf, loc)),
        BaseType::String => ForwardsUOffset::<&str>::follow(buf, loc)
            .parse::<f64>()
            .ok(),
        _ => None,
    }
}

/// Reads value as a string from the provided byte slice at the specified location.
///
/// # Safety
///
/// Caller must ensure `buf.len() >= loc + size_of::<T>()` at all the access layers.
unsafe fn get_any_value_string(
    base_type: BaseType,
    buf: &[u8],
    loc: usize,
    schema: &Schema,
    type_index: usize,
) -> String {
    match base_type {
        BaseType::Float | BaseType::Double => get_any_value_float(base_type, buf, loc)
            .unwrap_or_default()
            .to_string(),
        BaseType::String => ForwardsUOffset::<&str>::follow(buf, loc).to_string(),
        BaseType::Obj => {
            // Converts the table to a string. This is mostly for debugging purposes,
            // and does NOT promise to be JSON compliant.
            // Also prefixes the type.
            let object: Object = schema.objects().get(type_index);
            let mut s = object.name().to_string();
            s += " { ";
            if object.is_struct() {
                let st: Struct<'_> = Struct::follow(buf, loc);
                for field in object.fields() {
                    let field_value = get_any_field_string_in_struct(&st, &field, schema);
                    s += field.name();
                    s += ": ";
                    s += field_value.as_str();
                    s += ", ";
                }
            } else {
                let table = ForwardsUOffset::<Table>::follow(buf, loc);
                for field in object.fields() {
                    if table.vtable().get(field.offset()) == 0 {
                        continue;
                    }
                    let mut field_value = get_any_field_string(&table, &field, schema);
                    if field.type_().base_type() == BaseType::String {
                        field_value = escape(field_value.as_str()).to_string();
                    }
                    s += field.name();
                    s += ": ";
                    s += field_value.as_str();
                    s += ", ";
                }
            }
            s + "}"
        }
        BaseType::Vector => String::from("[(elements)]"), // TODO inherited from C++: implement this as well.
        BaseType::Union => String::from("(union)"), // TODO inherited from C++: implement this as well.
        _ => get_any_value_integer(base_type, buf, loc)
            .unwrap_or_default()
            .to_string(),
    }
}
