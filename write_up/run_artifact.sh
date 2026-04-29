#!/bin/sh

set -eu

bench_dir="${JSONIFIABLE_BENCH_DIR:-_build/jsonifiable-stdlib-bench}"
probe_timeout="${JSONIFIABLE_PROBE_TIMEOUT:-45}"
libraries="${JSONIFIABLE_LIBRARIES:-both}"

if command -v opam >/dev/null 2>&1; then
  eval "$(opam env)"
fi

echo "== rocq-json artifact: clean build =="
dune clean
dune build --display=short

echo "== rocq-json artifact: Corelib/Stdlib applicability benchmark =="
python3 scripts/bench_jsonifiable_stdlib.py \
  --out-dir "$bench_dir" \
  --libraries "$libraries" \
  --probe-timeout "$probe_timeout"

echo "== rocq-json artifact: extracted enum_256 benchmark =="
dune build --display=short _build/default/extracting/benched.stamp

echo "== rocq-json artifact: generate paper result snippets =="
python3 scripts/make_paper_results.py \
  --bench-dir "$bench_dir" \
  --extraction-csv _build/default/extracting/extraction_bench.csv \
  --out write_up/generated/results.tex

echo "== output files =="
printf '%s\n' \
  "$bench_dir/summary.json" \
  "$bench_dir/probe_results.csv" \
  "$bench_dir/benchmark_timings.csv" \
  "$bench_dir/failures.md" \
  "_build/default/extracting/extraction_bench.csv" \
  "write_up/generated/results.tex"
