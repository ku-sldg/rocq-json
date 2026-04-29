#!/bin/sh

set -eu

runs="${JSONIFIABLE_EXTRACTION_RUNS:-10}"
csv="extraction_bench.csv"

echo "benchmark,run,seconds" > "$csv"

run_one() {
  name="$1"
  exe="$2"
  run="$3"

  output="$("./$exe")"
  printf '%s\n' "$output"
  seconds="$(printf '%s\n' "$output" | sed -n 's/^JSON round-trip time: \([0-9.][0-9.]*\) s$/\1/p')"
  if [ -z "$seconds" ]; then
    echo "could not parse runtime from $exe output" >&2
    exit 1
  fi
  printf '%s,%s,%s\n' "$name" "$run" "$seconds" >> "$csv"
}

run=1
while [ "$run" -le "$runs" ]; do
  echo "Running harness.exe... generated run $run/$runs"
  run_one enum256_generated harness.exe "$run"
  echo "Running harness_2.exe... handwritten run $run/$runs"
  run_one enum256_handwritten harness_2.exe "$run"
  run=$((run + 1))
done

echo "Running harness_suite.exe... mixed-shape generated/handwritten benchmarks"
./harness_suite.exe | while IFS=' ' read -r tag name seconds; do
  printf '%s %s %s\n' "$tag" "$name" "$seconds"
  if [ "$tag" = "BENCH" ]; then
    printf '%s,1,%s\n' "$name" "$seconds" >> "$csv"
  fi
done

touch benched.stamp
