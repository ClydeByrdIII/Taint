#!/bin/bash

fname=$1
rm -f llvmprof.out # Otherwise your profile runs are added together

clang -emit-llvm -o $fname.bc -c $fname.c || { echo "Failed to emit llvm bc"; exit 1; }
opt -loop-simplify < $fname.bc > $fname.ls.bc || { echo "Failed to opt loop simplify"; exit 1; } 
opt -insert-edge-profiling $fname.ls.bc -o $fname.profile.ls.bc
llc $fname.profile.ls.bc -o $fname.profile.ls.s
g++ -o $fname.profile $fname.profile.ls.s /opt/llvm/Release+Asserts/lib/libprofile_rt.so
./$fname.profile $2 $3 $4

opt -load Release+Asserts/lib/mypass.so -profile-loader -profile-info-file=llvmprof.out -taint < $fname.ls.bc > /dev/null || { echo "Failed to opt-load"; exit 1; }
