# rocq-json Artifact

This artifact is designed to make the paper results reproducible without hiding unsupported cases.  It rebuilds the project, probes Rocq Corelib/Stdlib inductive-like declarations, classifies failures, compiles the successful derivations into one benchmark file, runs generated-vs-handwritten extraction benchmarks where both sides are written in Rocq, and regenerates the LaTeX result macros used by the paper draft.

## Dependencies and Supported Platforms

The Docker workflow is the recommended evaluation path.  It requires Docker and
does not assume a preconfigured opam switch on the host.

The native workflow has been tested on Linux with:

- Rocq/Coq 8.20 or later
- OCaml 4.12 or later
- dune 3.17 or later
- python3
- the opam dependencies listed in `rocq-json.opam`

## Docker Evaluation

Build the artifact image from the repository root:

```sh
docker build -f Dockerfile.artifact -t rocq-json-artifact .
```

Run the full evaluation:

```sh
docker run --rm rocq-json-artifact
```

The full run performs many isolated Rocq probes and can take several minutes.  To shorten a debugging run, override the probed libraries or timeout:

```sh
docker run --rm \
  -e JSONIFIABLE_LIBRARIES=corelib \
  -e JSONIFIABLE_PROBE_TIMEOUT=20 \
  rocq-json-artifact
```

## Native Evaluation

Install the released package with opam:

```sh
opam repo add -a --set-default ku-sldg/opam-repo https://github.com/ku-sldg/opam-repo.git
opam repo add coq-released https://coq.inria.fr/opam/released
opam install rocq-json
```

To evaluate this repository snapshot directly, install the dependencies and run:

```sh
opam install -y --deps-only ./rocq-json.opam
sh write_up/run_artifact.sh
```

The script assumes `dune`, `rocq`, `python3`, and the opam dependencies from `rocq-json.opam` are available.

## Minimal User Example

After installing `rocq-json`, a user can derive an instance for a fresh type:

```coq
From RocqJSON Require Import JSON JSON_Derive.

Inductive UserRole : Type :=
| Admin
| Moderator (level : nat)
| Guest.

Elpi derive.jsonifiable UserRole.

Example moderator_roundtrip :
  from_JSON (to_JSON (Moderator 2)) = res (Moderator 2) :=
  canonical_jsonification (Moderator 2).
```

If derivation fails, the Rocq error message identifies the first recognized
unsupported shape, such as a dependent constructor field, function-valued field,
proof field, sort-valued field, or Prop target.

## Outputs

The main output files are:

- `_build/jsonifiable-stdlib-bench/summary.json`: aggregate applicability and timing summary.
- `_build/jsonifiable-stdlib-bench/probe_results.csv`: one row per probed declaration.
- `_build/jsonifiable-stdlib-bench/benchmark_timings.csv`: successful derivations and Rocq `Time` measurements.
- `_build/jsonifiable-stdlib-bench/failures.md`: categorized diagnostics for unsupported or failed declarations.
- `_build/default/extracting/extraction_bench.csv`: repeated extracted OCaml timings for generated and handwritten Rocq definitions.
- `write_up/generated/results.tex`: LaTeX macros and table rows consumed by `write_up/paper.tex`.

## Interpreting Failures

Probe failures are not all claimed to be invalid inputs.  The categories are a triage aid:

- Some are semantic non-targets for the current interface, such as `prop-target-not-supported` and `coinductive-not-supported`.
- Some are current implementation limitations, such as `dependent-field-not-supported`, `indexed-family-not-supported`, `proof-field-not-supported`, `sort-field-not-supported`, and `function-field-not-supported`.
- Some are benchmark harness limitations, such as `scanner-or-logical-path`.

The generated `failures.md` file gives every failed declaration, its category, the source location, the probe file, and the captured Rocq diagnostic.  The generated paper macros also include one representative example per category.

The supported subset is the set of declarations that successfully compile in isolation and then compile again in the combined generated benchmark file.  The paper should report both the success count and the categorized failure count.

## Expected Results

On the development machine used while drafting, the broad benchmark discovered hundreds of Corelib/Stdlib declarations, successfully derived around one hundred `Jsonifiable` instances, and compiled the combined successful benchmark in a few seconds.  The extracted generated code was compared with handwritten Rocq baselines on a large enum, tuple-like constructor, mixed sum, and recursive tree.  The sample count is controlled by `JSONIFIABLE_EXTRACTION_RUNS` and defaults to 10.

Exact numbers should be taken from the generated files for the final submitted artifact and paper.
