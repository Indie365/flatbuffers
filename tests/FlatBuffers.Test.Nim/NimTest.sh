nim_dir=`pwd`
cd ..
test_dir=`pwd`
alias flatc='${test_dir}/../build/flatc'
shopt -s expand_aliases

mkdir -p ${nim_dir}/generated
cd ${nim_dir}/generated/
flatc --nim --gen-mutable -I ${test_dir}/include_test ${test_dir}/monster_test.fbs
# ${test_dir}/union_vector/union_vector.fbs
flatc --nim ${test_dir}/optional_scalars.fbs
flatc --nim ${test_dir}/more_defaults.fbs
flatc --nim --gen-mutable ${test_dir}/MutatingBool.fbs
cd ${nim_dir}

testament all
rm -rf ${nim_dir}/generated

# nim r tests/test_mutating_bool.nim
# nim r tests/test_my_game.nim
# nim r tests/test_more_defaults.nim
# nim r tests/test_optional_scalars.nim
# rm -rf ${nim_dir}/tests/MyGame ${nim_dir}/tests/optional_scalars ${nim_dir}/tests/*_generated.nim
