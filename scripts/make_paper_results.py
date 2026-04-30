#!/usr/bin/env python3
"""Generate LaTeX result snippets for the ATVA tool paper.

The script intentionally reads the same machine-readable files produced by the
artifact workflow.  This keeps paper tables tied to reproducible runs instead
of hand-copied numbers.
"""

from __future__ import annotations

import argparse
import csv
import json
import statistics
from collections import Counter
from pathlib import Path

CATEGORY_RATIONALES = {
    "prop-target-not-supported": "Targets live in Prop, while Jsonifiable builds computational data in Type.",
    "indexed-family-not-supported": "The declaration is a family indexed by values, not a plain data type after parameters.",
    "prop-indexed-family-not-supported": "The declaration is a predicate or relation family whose remaining indices end in Prop or SProp.",
    "dependent-field-not-supported": "A constructor field type depends on an earlier constructor argument, so a plain JSON decoder cannot reconstruct the dependent evidence.",
    "uncategorized-to-json-failure": "The to_json generator failed before emitting one of the known semantic diagnostics; this should not appear in a clean benchmark run.",
    "to-json-elaboration-failed": "Rocq rejected the generated term; these are possible deriver gaps or unsupported dependent shapes.",
    "proof-field-not-supported": "A constructor field lives in Prop or SProp, so the ordinary data round-trip contract would require proof erasure or proof reconstruction.",
    "sort-field-not-supported": "A constructor field is itself a sort such as Type or Set, while Jsonifiable serializes data values rather than type-level objects.",
    "function-field-not-supported": "A constructor field is function-valued, and there is no generic JSON encoding for arbitrary functions.",
    "from-json-elaboration-failed": "Rocq rejected the generated decoder; these are remaining deriver gaps requiring inspection.",
    "uncategorized-record-failure": "The record generator failed before emitting one of the known semantic diagnostics; this should not appear in a clean benchmark run.",
    "scanner-or-logical-path": "The benchmark scanner found a source declaration whose guessed logical path is not directly derivable.",
    "universe-polymorphism-not-supported": "The declaration uses universe behavior outside the current monomorphic deriver path.",
    "coinductive-not-supported": "The declaration is potentially infinite data, while the deriver targets inductive data.",
    "timeout": "The probe did not finish within the configured timeout and must be reviewed separately.",
    "other": "The diagnostic did not match a known category and should be treated as unresolved.",
}


def latex_escape(value: object) -> str:
    text = str(value)
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(char, char) for char in text)


def command(name: str, value: object) -> str:
    return rf"\newcommand{{\{name}}}{{{latex_escape(value)}}}"


def read_csv(path: Path) -> list[dict[str, str]]:
    if not path.exists():
        return []
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle))


def fmt_seconds(value: float | None) -> str:
    if value is None:
        return "n/a"
    if value < 0.001:
        return f"{value:.6f}"
    if value < 0.01:
        return f"{value:.4f}"
    if value < 1:
        return f"{value:.3f}"
    return f"{value:.2f}"


def fmt_extraction_seconds(value: float | None) -> str:
    if value is None:
        return "n/a"
    return f"{value:.6f}"


def percentile(values: list[float], pct: float) -> float | None:
    if not values:
        return None
    values = sorted(values)
    index = round((len(values) - 1) * pct)
    return values[index]


def timing_table_rows(rows: list[dict[str, str]], limit: int) -> list[str]:
    sorted_rows = sorted(rows, key=lambda row: float(row["rocq_time_seconds"]), reverse=True)
    out: list[str] = []
    for row in sorted_rows[:limit]:
        out.append(
            " & ".join(
                [
                    latex_escape(row["logical_name"]),
                    latex_escape(row["kind"]),
                    fmt_seconds(float(row["rocq_time_seconds"])),
                ]
            )
            + r" \\"
        )
    return out


def failure_example_rows(rows: list[dict[str, str]]) -> list[str]:
    examples: dict[str, dict[str, str]] = {}
    counts: Counter[str] = Counter()
    for row in rows:
        if row.get("status") == "ok":
            continue
        category = row.get("category") or "other"
        counts[category] += 1
        examples.setdefault(category, row)

    out: list[str] = []
    for category, count in sorted(counts.items(), key=lambda item: (-item[1], item[0])):
        row = examples[category]
        out.append(
            " & ".join(
                [
                    latex_escape(category),
                    str(count),
                    latex_escape(row.get("logical_name", "")),
                    latex_escape(CATEGORY_RATIONALES.get(category, CATEGORY_RATIONALES["other"])),
                ]
            )
            + r" \\"
        )
    return out


def extraction_summary(path: Path) -> tuple[dict[str, str], list[dict[str, str]]]:
    rows = read_csv(path)
    if not rows:
        return {}, []
    by_name: dict[str, list[float]] = {}
    for row in rows:
        by_name.setdefault(row["benchmark"], []).append(float(row["seconds"]))
    summary = {
        f"{name}_runs": str(len(values))
        for name, values in by_name.items()
    }
    for name, values in by_name.items():
        summary[f"{name}_mean"] = fmt_extraction_seconds(statistics.mean(values))
        summary[f"{name}_median"] = fmt_extraction_seconds(statistics.median(values))
        summary[f"{name}_min"] = fmt_extraction_seconds(min(values))
        summary[f"{name}_max"] = fmt_extraction_seconds(max(values))
    return summary, rows


def extraction_table_rows(rows: list[dict[str, str]]) -> list[str]:
    by_name: dict[str, list[float]] = {}
    for row in rows:
        by_name.setdefault(row["benchmark"], []).append(float(row["seconds"]))
    out: list[str] = []
    preferred_bases = ["enum256", "point2d", "userrole", "serverconfig", "instruction", "bintree"]
    all_bases = {name.rsplit("_", 1)[0] for name in by_name}
    bases = preferred_bases + sorted(all_bases.difference(preferred_bases))
    first_group = True
    for base in bases:
        names = [f"{base}_generated", f"{base}_handwritten"]
        names.extend(sorted(name for name in by_name if name.startswith(f"{base}_") and name not in names))
        present_names = [name for name in names if name in by_name]
        if not present_names:
            continue
        if not first_group:
            out.append(r"\midrule")
        first_group = False
        for name in present_names:
            values = by_name[name]
            out.append(
                " & ".join(
                    [
                        latex_escape(name),
                        str(len(values)),
                        fmt_extraction_seconds(statistics.mean(values)),
                        fmt_extraction_seconds(statistics.median(values)),
                        fmt_extraction_seconds(min(values)),
                        fmt_extraction_seconds(max(values)),
                    ]
                )
                + r" \\"
            )
    for name in sorted(name for name in by_name if name.rsplit("_", 1)[0] not in bases):
        values = by_name[name]
        out.append(
            " & ".join(
                [
                    latex_escape(name),
                    str(len(values)),
                    fmt_extraction_seconds(statistics.mean(values)),
                    fmt_extraction_seconds(statistics.median(values)),
                    fmt_extraction_seconds(min(values)),
                    fmt_extraction_seconds(max(values)),
                ]
            )
            + r" \\"
        )
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bench-dir", type=Path, default=Path("_build/jsonifiable-stdlib-bench"))
    parser.add_argument("--extraction-csv", type=Path, default=Path("_build/default/extracting/extraction_bench.csv"))
    parser.add_argument("--out", type=Path, default=Path("write_up/generated/results.tex"))
    parser.add_argument("--top", type=int, default=8)
    args = parser.parse_args()

    summary_path = args.bench_dir / "summary.json"
    timings_path = args.bench_dir / "benchmark_timings.csv"
    if not summary_path.exists():
        raise SystemExit(f"missing benchmark summary: {summary_path}")
    if not timings_path.exists():
        raise SystemExit(f"missing benchmark timings: {timings_path}")

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    timing_rows = read_csv(timings_path)
    probe_rows = read_csv(args.bench_dir / "probe_results.csv")
    times = [float(row["rocq_time_seconds"]) for row in timing_rows]
    kinds = Counter(row["kind"] for row in timing_rows)
    libraries = Counter(row["library"] for row in timing_rows)
    extraction, extraction_rows = extraction_summary(args.extraction_csv)

    lines = [
        "% Generated by scripts/make_paper_results.py.",
        "% Re-run the artifact workflow before submitting final numbers.",
        command("JsonifiableDiscovered", summary.get("discovered", "n/a")),
        command("JsonifiableProbed", summary.get("probed", "n/a")),
        command("JsonifiableProbeSuccesses", summary.get("probe_successes", "n/a")),
        command("JsonifiableProbeFailures", summary.get("probe_failures", "n/a")),
        command("JsonifiableProbeTimeouts", summary.get("probe_timeouts", "n/a")),
        command("JsonifiableTimedDerivations", summary.get("timed_derivations", "n/a")),
        command("JsonifiableBenchmarkWallSeconds", fmt_seconds(summary.get("benchmark_wall_seconds"))),
        command("JsonifiableDerivationSumSeconds", fmt_seconds(summary.get("sum_rocq_time_seconds"))),
        command("JsonifiableDerivationMeanSeconds", fmt_seconds(summary.get("mean_rocq_time_seconds"))),
        command("JsonifiableDerivationMedianSeconds", fmt_seconds(statistics.median(times) if times else None)),
        command("JsonifiableDerivationPNineZeroSeconds", fmt_seconds(percentile(times, 0.90))),
        command("JsonifiableDerivationMaxSeconds", fmt_seconds(summary.get("max_rocq_time_seconds"))),
        command("JsonifiableSuccessInductives", kinds.get("Inductive", 0)),
        command("JsonifiableSuccessVariants", kinds.get("Variant", 0)),
        command("JsonifiableSuccessRecords", kinds.get("Record", 0) + kinds.get("Structure", 0)),
        command("JsonifiableSuccessCorelib", libraries.get("Corelib", 0)),
        command("JsonifiableSuccessStdlib", libraries.get("Stdlib", 0)),
        command("JsonifiableExtractionGeneratedRuns", extraction.get("enum256_generated_runs", "n/a")),
        command("JsonifiableExtractionGeneratedMean", extraction.get("enum256_generated_mean", "n/a")),
        command("JsonifiableExtractionGeneratedMedian", extraction.get("enum256_generated_median", "n/a")),
        command("JsonifiableExtractionHandwrittenRuns", extraction.get("enum256_handwritten_runs", "n/a")),
        command("JsonifiableExtractionHandwrittenMean", extraction.get("enum256_handwritten_mean", "n/a")),
        command("JsonifiableExtractionHandwrittenMedian", extraction.get("enum256_handwritten_median", "n/a")),
        "",
        r"\newcommand{\JsonifiableFailureRows}{%",
    ]
    for category, count in sorted(summary.get("failure_categories", {}).items(), key=lambda item: (-item[1], item[0])):
        lines.append(f"{latex_escape(category)} & {count}" + r" \\")
    lines.extend(
        [
            "}",
            "",
            r"\newcommand{\JsonifiableSlowestRows}{%",
            *timing_table_rows(timing_rows, args.top),
            "}",
            "",
            r"\newcommand{\JsonifiableFailureExampleRows}{%",
            *failure_example_rows(probe_rows),
            "}",
            "",
            r"\newcommand{\JsonifiableExtractionRows}{%",
            *extraction_table_rows(extraction_rows),
            "}",
            "",
        ]
    )

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
