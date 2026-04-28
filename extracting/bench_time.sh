#!/bin/sh

# First, run `harness.exe` and get its runtime, then `harness_2.exe` and get its runtime, and then compare the two.
# This script assumes that `harness.exe` and `harness_2.exe` are in the same directory as this script.
echo "Running harness.exe... (results for the non-hand written version)"
./harness.exe
echo "Running harness_2.exe... (results for the hand written version)"
./harness_2.exe

touch benched.stamp