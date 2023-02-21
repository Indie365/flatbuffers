/*
 * Copyright 2023 Google Inc. All rights reserved.
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

#include <string>
#include <set>
#include <fstream>

#include "flatbuffers/file_manager.h"

namespace flatbuffers {

class FileBinaryWriter : public FileManager {
 public:
  bool SaveFile(const std::string &absolute_file_name, const std::string &content) override {
    std::ofstream ofs(absolute_file_name,
                      std::ofstream::binary);
    if (!ofs.is_open()) return false;
    ofs.write(content.c_str(), content.size());
    if (!ofs.bad()) {
      file_names_.insert(absolute_file_name);
      return true;
    }
    return false;
  }

  bool ReadFile(const std::string &absolute_file_name, std::string *content) override {
    (void) absolute_file_name;
    (void) content;
    return false;
  }

  //std::set<std::string> FileNames() { return file_names_; }
};

}  // namespace flatbuffers
