# rocq-json ATVA Artifact

This artifact is designed to make the paper results reproducible without hiding unsupported cases.  It rebuilds the project, probes Rocq Corelib/Stdlib inductive-like declarations, classifies failures, compiles the successful derivations into one benchmark file, runs the extracted `enum_256` generated-vs-handwritten benchmark, and regenerates the LaTeX result macros used by the paper draft.

## Docker Evaluation

Build the artifact image from the repository root:

```sh
docker build -f Dockerfile.artifact -t rocq-json-atva-artifact .
```

Run the full evaluation:

```sh
docker run --rm rocq-json-atva-artifact
```

The full run performs many isolated Rocq probes and can take several minutes.  To shorten a debugging run, override the probed libraries or timeout:

```sh
docker run --rm \
  -e JSONIFIABLE_LIBRARIES=corelib \
  -e JSONIFIABLE_PROBE_TIMEOUT=20 \
  rocq-json-atva-artifact
```

## Native Evaluation

On a machine with the repository dependencies installed:

```sh
sh write_up/run_artifact.sh
```

The script assumes `dune`, `rocq`, `python3`, and the opam dependencies from `rocq-json.opam` are available.

## Outputs

The main output files are:

- `_build/jsonifiable-stdlib-bench/summary.json`: aggregate applicability and timing summary.
- `_build/jsonifiable-stdlib-bench/probe_results.csv`: one row per probed declaration.
- `_build/jsonifiable-stdlib-bench/benchmark_timings.csv`: successful derivations and Rocq `Time` measurements.
- `_build/jsonifiable-stdlib-bench/failures.md`: categorized diagnostics for unsupported or failed declarations.
- `_build/default/extracting/extraction_bench.csv`: repeated extracted OCaml generated-vs-handwritten `enum_256` timings.
- `write_up/generated/results.tex`: LaTeX macros and table rows consumed by `write_up/paper.tex`.

## Interpreting Failures

Probe failures are expected for declarations outside the current data fragment.  Common categories include `prop-target-not-supported`, indexed families, records with proof/function/Type-valued fields, scanner limitations for functor-local declarations, and coinductive types.  These are reported as part of the evaluation rather than filtered out after the fact.

The supported subset is the set of declarations that successfully compile in isolation and then compile again in the combined generated benchmark file.  The paper should report both the success count and the categorized failure count.

## Expected Results

On the development machine used while drafting, the broad benchmark discovered hundreds of Corelib/Stdlib declarations, successfully derived around one hundred `Jsonifiable` instances, and compiled the combined successful benchmark in a few seconds.  The extracted `enum_256` generated decoder ran within measurement noise of the handwritten decoder.

Exact numbers should be taken from the generated files for the final submitted artifact and paper.
