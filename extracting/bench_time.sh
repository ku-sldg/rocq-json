#!/bin/sh

set -eu

runs="${JSONIFIABLE_EXTRACTION_RUNS:-10}"
csv="extraction_bench.csv"

echo "benchmark,run,seconds" > "$csv"

run=1
while [ "$run" -le "$runs" ]; do
  echo "Running harness_suite.exe... run $run/$runs"
  ./harness_suite.exe | while IFS=' ' read -r tag name seconds; do
    printf '%s %s %s\n' "$tag" "$name" "$seconds"
    if [ "$tag" = "BENCH" ]; then
      printf '%s,%s,%s\n' "$name" "$run" "$seconds" >> "$csv"
    fi
  done
  run=$((run + 1))
done

touch benched.stamp
