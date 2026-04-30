#!/usr/bin/env python3
"""Benchmark Jsonifiable derivation over Rocq Corelib/Stdlib inductives.

The script discovers inductive-like declarations in the installed Rocq
Corelib/Stdlib sources, probes each candidate in isolation, then writes and
compiles a single benchmark artifact containing timed derivations for every
candidate that succeeded during probing.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


DECL_RE = re.compile(
    r"(?<!\bExtract\s)\b(?:Polymorphic\s+|Monomorphic\s+|Cumulative\s+|Private\s+)*"
    r"(Inductive|CoInductive|Variant|Record|Structure)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)"
)
WITH_RE = re.compile(r"^\s*with\s+([A-Za-z_][A-Za-z0-9_']*)")
MODULE_RE = re.compile(
    r"^\s*Module\s+(?:(?:Export|Import)\s+)?(?!(?:Type|Include)\b)([A-Za-z_][A-Za-z0-9_']*)\b"
)
END_RE = re.compile(r"^\s*End\s+([A-Za-z_][A-Za-z0-9_']*)\s*\.")
TIME_RE = re.compile(
    r"Finished transaction in\s+(-?[0-9.]+)\s+secs"
    r"(?:\s+\(([0-9.]+)u,([0-9.]*)s\))?"
)

FAILURE_CATEGORY_NOTES = {
    "prop-target-not-supported": (
        "expected",
        "The declaration lives in Prop. Jsonifiable produces computational JSON data in Type, and Prop values generally cannot be eliminated into Type.",
    ),
    "indexed-family-not-supported": (
        "expected-current-limitation",
        "The declaration is an indexed family, such as bool -> Set. The current deriver expects a fully applied target whose type is exactly Set or Type.",
    ),
    "to-json-generation-not-supported": (
        "expected-current-limitation",
        "The declaration falls outside the first-order data fragment handled by the generator, commonly because of subset/proof fields, SProp, aliases such as Ensemble, or unsupported dependent structure.",
    ),
    "proof-field-not-supported": (
        "expected-current-limitation",
        "At least one constructor has a field whose type lives in Prop or SProp. The current Jsonifiable contract round-trips computational data and does not erase or reconstruct proofs.",
    ),
    "record-generation-not-supported": (
        "expected-current-limitation",
        "The record has fields that are not plain serializable data, such as proof fields, function fields, Type-valued fields, or dependent fields.",
    ),
    "to-json-elaboration-failed": (
        "expected-current-limitation-or-review",
        "Rocq rejected the generated to_json term. In the current Corelib/Stdlib run these cases are indexed/dependent families, relation/function parameters, or records over value parameters.",
    ),
    "from-json-elaboration-failed": (
        "expected-current-limitation-or-review",
        "Rocq rejected the generated from_json term. Inspect the captured diagnostic to decide whether the declaration is outside the supported fragment or exposes a deriver bug.",
    ),
    "scanner-or-logical-path": (
        "scanner-limitation",
        "The source scanner found a declaration whose constructed logical path is not directly addressable, typically because it is inside a functor, module type, or locally encapsulated module.",
    ),
    "universe-polymorphism-not-supported": (
        "expected-current-limitation",
        "The declaration uses universe behavior that the deriver does not currently support, including SProp/universe-polymorphic cases.",
    ),
    "coinductive-not-supported": (
        "expected-current-limitation",
        "The declaration is coinductive. The current Jsonifiable derivation handles inductive data, not potentially infinite coinductive values.",
    ),
    "timeout": (
        "needs-review",
        "The probe timed out before Rocq produced a result.",
    ),
    "other": (
        "needs-review",
        "The failure did not match a known diagnostic category. Inspect the full log before classifying it as expected.",
    ),
}


@dataclass(frozen=True)
class Candidate:
    library: str
    kind: str
    target_sort: str
    arity: str
    has_prop_argument: bool
    has_indices: bool
    has_non_sort_parameter: bool
    has_untyped_parameter: bool
    record_data_issue: str
    import_module: str
    module: str
    name: str
    source: str
    line: int

    @property
    def logical_name(self) -> str:
        return f"{self.module}.{self.name}"


@dataclass
class ProbeResult:
    library: str
    kind: str
    target_sort: str
    arity: str
    has_prop_argument: bool
    has_indices: bool
    has_non_sort_parameter: bool
    has_untyped_parameter: bool
    record_data_issue: str
    module: str
    name: str
    logical_name: str
    source: str
    line: int
    status: str
    seconds: float
    rocq_time_seconds: float | None
    category: str
    message: str
    probe_file: str
    log_file: str


def run(cmd: list[str], cwd: Path | None = None, timeout: int | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        timeout=timeout,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def rocq_config(rocq: str) -> dict[str, str]:
    proc = run([rocq, "c", "--config"])
    if proc.returncode != 0:
        raise RuntimeError(proc.stdout)
    config: dict[str, str] = {}
    for line in proc.stdout.splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            config[key.strip()] = value.strip()
    if "COQLIB" not in config:
        raise RuntimeError("rocq c --config did not report COQLIB")
    return config


def strip_comments(text: str) -> str:
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        two = text[i : i + 2]
        if two == "(*":
            depth += 1
            out.append("  ")
            i += 2
        elif depth and two == "*)":
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def source_to_module(root_name: str, root: Path, path: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    return ".".join([root_name, *rel.parts])


def declaration_snippet(lines: list[str], line_index: int) -> str:
    chunks: list[str] = []
    for line in lines[line_index:]:
        chunks.append(line.strip())
        if "." in line:
            break
    return " ".join(chunks)


def declaration_header(snippet: str) -> str:
    return snippet.split(":=", 1)[0].rsplit(".", 1)[0].strip()


def final_top_level_colon(header: str) -> int | None:
    depth = 0
    last_colon: int | None = None
    for index, char in enumerate(header):
        if char in "([{":
            depth += 1
        elif char in ")]}" and depth > 0:
            depth -= 1
        elif char == ":" and depth == 0:
            last_colon = index
    return last_colon


def declaration_arity(snippet: str) -> str:
    header = declaration_header(snippet)
    colon = final_top_level_colon(header)
    if colon is None:
        return "Type"
    return header[colon + 1 :].strip()


def declaration_target_sort(snippet: str) -> str:
    arity = declaration_arity(snippet)
    match = re.search(r"\b(Prop|Set|Type(?:@\{[^}]+\})?)\s*$", arity)
    if not match:
        return "unknown"
    sort = match.group(1)
    if sort.startswith("Type"):
        return "Type"
    return sort


def declaration_has_prop_argument(snippet: str) -> bool:
    header = declaration_header(snippet)
    colon = final_top_level_colon(header)
    before_final_arity = header if colon is None else header[:colon]
    return bool(re.search(r"\bProp\b", before_final_arity))


def declaration_has_indices(snippet: str) -> bool:
    arity = declaration_arity(snippet)
    return not bool(re.fullmatch(r"(Prop|Set|Type(?:@\{[^}]+\})?)", arity))


def parameter_surface(snippet: str) -> str:
    header = declaration_header(snippet)
    colon = final_top_level_colon(header)
    return header if colon is None else header[:colon]


def binder_type_is_sort(ty: str) -> bool:
    return bool(re.fullmatch(r"(Set|Type(?:@\{[^}]+\})?)", ty.strip()))


def declaration_has_non_sort_parameter(snippet: str) -> bool:
    surface = parameter_surface(snippet)
    for match in re.finditer(r"[\(\{]([^()\{\}]*)[\)\}]", surface):
        binder = match.group(1)
        if ":" not in binder:
            continue
        ty = binder.rsplit(":", 1)[1].strip()
        if not binder_type_is_sort(ty):
            return True
    return False


def mask_binders(surface: str) -> str:
    out: list[str] = []
    depth = 0
    for char in surface:
        if char in "({":
            depth += 1
            out.append(" ")
        elif char in ")}" and depth > 0:
            depth -= 1
            out.append(" ")
        elif depth:
            out.append(" ")
        else:
            out.append(char)
    return "".join(out)


def untyped_parameter_names(kind: str, name: str, snippet: str) -> list[str]:
    surface = mask_binders(parameter_surface(snippet))
    match = re.search(rf"\b{re.escape(kind)}\s+{re.escape(name)}\b(?P<rest>.*)$", surface)
    if not match:
        return []
    rest = match.group("rest")
    return re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*\b", rest)


def declaration_has_untyped_parameter(kind: str, name: str, snippet: str) -> bool:
    return bool(untyped_parameter_names(kind, name, snippet))


def top_level_brace_content(text: str) -> str | None:
    start = text.find("{")
    if start < 0:
        return None
    depth = 0
    for index in range(start, len(text)):
        char = text[index]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1 : index]
    return None


def split_top_level_semicolons(text: str) -> list[str]:
    fields: list[str] = []
    depth = 0
    start = 0
    for index, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}" and depth > 0:
            depth -= 1
        elif char == ";" and depth == 0:
            field = text[start:index].strip()
            if field:
                fields.append(field)
            start = index + 1
    tail = text[start:].strip()
    if tail:
        fields.append(tail)
    return fields


def split_field(field: str) -> tuple[list[str], str] | None:
    colon = field.find(":")
    if colon < 0:
        return None
    names_part = field[:colon].replace(":>", " ").strip()
    ty = field[colon + 1 :].strip()
    if ty.startswith(">"):
        ty = ty[1:].strip()
    names = [name for name in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", names_part) if name != "_"]
    return names, ty


def field_type_is_sort(ty: str) -> bool:
    return bool(re.fullmatch(r"(Prop|Set|Type(?:@\{[^}]+\})?)", ty.strip()))


def field_type_is_function(ty: str) -> bool:
    return "->" in ty or bool(re.search(r"\bforall\b", ty))


def field_type_mentions(names: list[str], ty: str) -> bool:
    return any(re.search(rf"\b{re.escape(name)}\b", ty) for name in names)


def record_data_issue(kind: str, name: str, snippet: str) -> str:
    if kind not in {"Record", "Structure"}:
        return ""
    body = top_level_brace_content(snippet)
    if body is None:
        return "record-without-brace-fields"

    untyped_params = untyped_parameter_names(kind, name, snippet)
    previous_fields: list[str] = []
    for field in split_top_level_semicolons(body):
        parsed = split_field(field)
        if parsed is None:
            return "record-unparsed-field"
        names, ty = parsed
        if field.lstrip().startswith("_"):
            return "record-proof-or-unnamed-field"
        if field_type_is_sort(ty):
            return "record-sort-valued-field"
        if field_type_is_function(ty):
            return "record-function-field"
        if field_type_mentions(previous_fields, ty):
            return "record-dependent-field"
        if field_type_mentions(untyped_params, ty) and ty.strip() not in untyped_params:
            return "record-field-uses-untyped-parameter"
        previous_fields.extend(names)
    return ""


def make_candidate(
    root_name: str,
    kind: str,
    import_module: str,
    module: str,
    name: str,
    source: str,
    line_no: int,
    snippet: str,
) -> Candidate:
    arity = declaration_arity(snippet)
    sort = declaration_target_sort(snippet)
    return Candidate(
        root_name,
        kind,
        sort,
        arity,
        declaration_has_prop_argument(snippet),
        declaration_has_indices(snippet),
        declaration_has_non_sort_parameter(snippet),
        declaration_has_untyped_parameter(kind, name, snippet),
        record_data_issue(kind, name, snippet),
        import_module,
        module,
        name,
        source,
        line_no,
    )


def scan_file(root_name: str, root: Path, path: Path) -> list[Candidate]:
    raw = path.read_text(encoding="utf-8", errors="ignore")
    text = strip_comments(raw)
    base_module = source_to_module(root_name, root, path)
    import_module = base_module
    source = str(path)
    stack: list[str] = []
    candidates: list[Candidate] = []
    active_inductive_decl = False
    lines = text.splitlines()

    for line_index, line in enumerate(lines):
        line_no = line_index + 1
        end_match = END_RE.match(line)
        if end_match and stack:
            ended = end_match.group(1)
            if stack[-1] == ended:
                stack.pop()
            elif ended in stack:
                stack = stack[: stack.index(ended)]

        module_match = MODULE_RE.match(line)
        if module_match and ":=" not in line:
            stack.append(module_match.group(1))

        module = ".".join([base_module, *stack])
        decl_matches = list(DECL_RE.finditer(line))
        for match in decl_matches:
            snippet = declaration_snippet(lines, line_index)
            candidates.append(make_candidate(root_name, match.group(1), import_module, module, match.group(2), source, line_no, snippet))
        if decl_matches:
            active_inductive_decl = True
        if active_inductive_decl:
            for match in WITH_RE.finditer(line):
                snippet = declaration_snippet(lines, line_index)
                candidates.append(make_candidate(root_name, "with", import_module, module, match.group(1), source, line_no, snippet))
        if active_inductive_decl and "." in line:
            active_inductive_decl = False

    return candidates


def discover(root_name: str, root: Path) -> list[Candidate]:
    found: list[Candidate] = []
    for path in sorted(root.rglob("*.v")):
        found.extend(scan_file(root_name, root, path))

    seen: set[str] = set()
    unique: list[Candidate] = []
    for candidate in found:
        if candidate.logical_name not in seen:
            unique.append(candidate)
            seen.add(candidate.logical_name)
    return unique


def require_line(candidate: Candidate) -> str:
    parts = candidate.import_module.split(".")
    return f"From {parts[0]} Require Import {'.'.join(parts[1:])}."


def file_prelude() -> str:
    return "\n".join(
        [
            "From RocqJSON Require Import JSON JSON_Derive JSON_Error_Strings.",
            "Local Open Scope string_scope.",
            "Set Warnings \"-notation-overridden,-require-in-module\".",
            "",
        ]
    )


def derive_command(candidate: Candidate) -> str:
    return f'Time Elpi derive.jsonifiable "{candidate.logical_name}".'


def rocq_args(repo: Path, rocq_json_root: Path | None, derivers_root: Path | None) -> list[str]:
    args: list[str] = []
    if rocq_json_root:
        args.extend(["-Q", str(rocq_json_root), "RocqJSON"])
    if derivers_root:
        args.extend(["-Q", str(derivers_root), "rocq_json_derivers"])
    return args


def detect_build_roots(repo: Path) -> tuple[Path | None, Path | None]:
    theories = repo / "_build" / "default" / "theories"
    derivers = repo / "_build" / "default" / "derivers"
    return (
        theories if (theories / "JSON_Derive.vo").exists() else None,
        derivers if (derivers / "jsonifiable.elpi").exists() else None,
    )


def last_error(output: str) -> str:
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    if not lines:
        return ""

    for idx, line in enumerate(lines):
        if line.startswith("Error:") or "Error:" in line:
            detail = "\n".join(lines[idx : idx + 12])
            return detail[:2000]
    return "\n".join(lines[-12:])[:2000]


def classify_failure(candidate: Candidate, output: str, status: str) -> str:
    if status == "ok":
        return "ok"
    if status == "timeout":
        return "timeout"

    text = output.lower()
    if candidate.target_sort == "Prop":
        return "prop-target-not-supported"
    if candidate.kind == "CoInductive":
        return "coinductive-not-supported"
    if "cannot be called on a constant" in text:
        return "not-an-inductive"
    if "global reference not found" in text:
        return "scanner-or-logical-path"
    if "which should be set, prop or type" in text:
        return "indexed-family-not-supported"
    if "expected: closed_term" in text:
        return "generated-open-term"
    if "universe polymorphic gref" in text:
        return "universe-polymorphism-not-supported"
    if "unsupported nested recursive occurrence" in text:
        return "unsupported-nested-recursion"
    if "proof/sprop constructor fields are not supported" in text:
        return "proof-field-not-supported"
    if "canonical_jsonification proof could not be closed" in text or "proof incomplete" in text:
        return "proof-not-closed"
    if "build-to-json-term failed" in text:
        return "to-json-generation-not-supported"
    if "build-record-fun-wrapped failed" in text:
        return "record-generation-not-supported"
    if "to_json elaboration failed" in text:
        return "to-json-elaboration-failed"
    if "from_json elaboration failed" in text:
        return "from-json-elaboration-failed"
    return "other"


def parse_rocq_time_match(match: re.Match[str]) -> float:
    """Return a non-negative elapsed time from Rocq's Time output.

    Rocq can occasionally print a negative wall-clock time.  Keeping the row is
    more important than preserving that bogus wall value, since otherwise later
    rows become misaligned.  When this happens and user/system CPU fields are
    present, use their sum as the best available per-transaction cost.
    """

    wall = float(match.group(1))
    if wall >= 0:
        return wall
    user = float(match.group(2) or 0)
    system = float(match.group(3) or 0)
    return user + system


def rocq_times(output: str) -> list[float]:
    return [parse_rocq_time_match(match) for match in TIME_RE.finditer(output)]


def rocq_time(output: str) -> float | None:
    times = rocq_times(output)
    return times[-1] if times else None


def safe_path_part(value: str) -> str:
    safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", value)
    return safe[:180].strip("._") or "candidate"


def safe_module_name(index: int, candidate: Candidate) -> str:
    safe = re.sub(r"[^A-Za-z0-9_]+", "_", candidate.logical_name).strip("_") or "Candidate"
    if safe[0].isdigit():
        safe = f"Candidate_{safe}"
    return f"JsonifiableBench_{index:05d}_{safe}"


def probe_candidate(
    candidate: Candidate,
    index: int,
    rocq: str,
    repo: Path,
    out_dir: Path,
    timeout: int,
    extra_rocq_args: list[str],
) -> ProbeResult:
    probe_dir = out_dir / "probes" / f"{index:05d}-{safe_path_part(candidate.logical_name)}"
    probe_dir.mkdir(parents=True, exist_ok=True)
    probe_file = probe_dir / "Probe.v"
    log_file = probe_dir / "rocq.log"
    probe_file.write_text(
        "\n".join(
            [
                file_prelude(),
                f"(* candidate: {candidate.logical_name}",
                f"   kind: {candidate.kind}",
                f"   target sort: {candidate.target_sort}",
                f"   arity: {candidate.arity}",
                f"   has Prop argument: {candidate.has_prop_argument}",
                f"   has indices: {candidate.has_indices}",
                f"   has non-sort parameter: {candidate.has_non_sort_parameter}",
                f"   has untyped parameter: {candidate.has_untyped_parameter}",
                f"   record data issue: {candidate.record_data_issue or 'none'}",
                f"   source: {candidate.source}:{candidate.line} *)",
                require_line(candidate),
                derive_command(candidate),
                "",
            ]
        ),
        encoding="utf-8",
    )
    cmd = [rocq, "c", *extra_rocq_args, str(probe_file)]
    start = time.perf_counter()
    try:
        proc = run(cmd, cwd=repo, timeout=timeout)
        elapsed = time.perf_counter() - start
        status = "ok" if proc.returncode == 0 else "fail"
        log_file.write_text(
            f"$ {' '.join(cmd)}\n\n{proc.stdout}",
            encoding="utf-8",
        )
        category = classify_failure(candidate, proc.stdout, status)
        message = "" if status == "ok" else last_error(proc.stdout)
        return ProbeResult(
            candidate.library,
            candidate.kind,
            candidate.target_sort,
            candidate.arity,
            candidate.has_prop_argument,
            candidate.has_indices,
            candidate.has_non_sort_parameter,
            candidate.has_untyped_parameter,
            candidate.record_data_issue,
            candidate.module,
            candidate.name,
            candidate.logical_name,
            candidate.source,
            candidate.line,
            status,
            elapsed,
            rocq_time(proc.stdout),
            category,
            message,
            str(probe_file),
            str(log_file),
        )
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        log_file.write_text(
            f"$ {' '.join(cmd)}\n\n{output}\n\ntimeout after {timeout}s\n",
            encoding="utf-8",
        )
        return ProbeResult(
            candidate.library,
            candidate.kind,
            candidate.target_sort,
            candidate.arity,
            candidate.has_prop_argument,
            candidate.has_indices,
            candidate.has_non_sort_parameter,
            candidate.has_untyped_parameter,
            candidate.record_data_issue,
            candidate.module,
            candidate.name,
            candidate.logical_name,
            candidate.source,
            candidate.line,
            "timeout",
            float(timeout),
            None,
            "timeout",
            f"timed out after {timeout}s",
            str(probe_file),
            str(log_file),
        )


def write_csv(path: Path, rows: Iterable[ProbeResult]) -> None:
    rows = list(rows)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(asdict(rows[0]).keys()) if rows else [])
        if rows:
            writer.writeheader()
            for row in rows:
                writer.writerow(asdict(row))


def write_benchmark_file(path: Path, candidates: list[Candidate]) -> None:
    lines = [
        "(* Generated by scripts/bench_jsonifiable_stdlib.py. *)",
        "(* This file contains timed Jsonifiable derivations for probed-successful Corelib/Stdlib inductives. *)",
        "",
        file_prelude(),
    ]
    for index, candidate in enumerate(candidates, start=1):
        module_name = safe_module_name(index, candidate)
        lines.extend(
            [
                f"(* {index}. {candidate.logical_name}",
                f"   kind: {candidate.kind}; target sort: {candidate.target_sort}",
                f"   arity: {candidate.arity}",
                f"   has non-sort parameter: {candidate.has_non_sort_parameter}",
                f"   has untyped parameter: {candidate.has_untyped_parameter}",
                f"   record data issue: {candidate.record_data_issue or 'none'}",
                f"   source: {candidate.source}:{candidate.line} *)",
                f"Module {module_name}.",
                require_line(candidate),
                derive_command(candidate),
                f"End {module_name}.",
                "",
            ]
        )
    path.write_text("\n".join(lines), encoding="utf-8")


def write_candidates_csv(path: Path, rows: Iterable[tuple[Candidate, str]]) -> None:
    rows = list(rows)
    with path.open("w", encoding="utf-8", newline="") as handle:
        fieldnames = [*list(asdict(rows[0][0]).keys()), "logical_name", "skip_reason"] if rows else []
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        if rows:
            writer.writeheader()
            for row, reason in rows:
                writer.writerow(asdict(row) | {"logical_name": row.logical_name, "skip_reason": reason})


def write_failure_report(path: Path, rows: list[ProbeResult]) -> None:
    failures = [row for row in rows if row.status != "ok"]
    lines = [
        "# Jsonifiable Stdlib/Corelib Probe Failures",
        "",
        "These are probe-time failures. The benchmark artifact intentionally excludes them so one unsupported type does not stop timing for the supported subset.",
        "",
    ]
    if not failures:
        lines.append("No probe failures.")
        path.write_text("\n".join(lines), encoding="utf-8")
        return

    category_counts: dict[str, int] = {}
    for row in failures:
        category_counts[row.category] = category_counts.get(row.category, 0) + 1

    lines.extend(["## Category Summary", ""])
    for category, count in sorted(category_counts.items(), key=lambda item: (-item[1], item[0])):
        disposition, explanation = FAILURE_CATEGORY_NOTES.get(category, FAILURE_CATEGORY_NOTES["other"])
        lines.extend(
            [
                f"### {category}",
                "",
                f"- count: `{count}`",
                f"- disposition: `{disposition}`",
                f"- explanation: {explanation}",
                "",
            ]
        )

    lines.extend(["## Individual Failures", ""])

    for row in failures:
        disposition, explanation = FAILURE_CATEGORY_NOTES.get(row.category, FAILURE_CATEGORY_NOTES["other"])
        lines.extend(
            [
                f"### {row.logical_name}",
                "",
                f"- status: `{row.status}`",
                f"- category: `{row.category}`",
                f"- disposition: `{disposition}`",
                f"- category explanation: {explanation}",
                f"- declaration kind: `{row.kind}`",
                f"- target sort: `{row.target_sort}`",
                f"- arity: `{row.arity}`",
                f"- has Prop argument: `{row.has_prop_argument}`",
                f"- has indices: `{row.has_indices}`",
                f"- has non-sort parameter: `{row.has_non_sort_parameter}`",
                f"- has untyped parameter: `{row.has_untyped_parameter}`",
                f"- record data issue: `{row.record_data_issue or 'none'}`",
                f"- source: `{row.source}:{row.line}`",
                f"- probe file: `{row.probe_file}`",
                f"- full log: `{row.log_file}`",
                "",
                "```text",
                row.message or "(no diagnostic captured)",
                "```",
                "",
            ]
        )
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rocq", default=os.environ.get("ROCQ", "rocq"), help="Rocq command, default: rocq")
    parser.add_argument("--repo", default=Path.cwd(), type=Path, help="rocq-json repository root")
    parser.add_argument("--out-dir", default=Path("_build/jsonifiable-stdlib-bench"), type=Path)
    parser.add_argument("--libraries", choices=["corelib", "stdlib", "both"], default="both")
    parser.add_argument("--limit", type=int, default=None, help="limit candidates, useful for smoke tests")
    parser.add_argument("--probe-timeout", type=int, default=45)
    parser.add_argument("--skip-dune-build", action="store_true")
    parser.add_argument(
        "--data-like-only",
        action="store_true",
        help="skip declarations outside the conservative data-like fragment; by default every discovered declaration is probed",
    )
    parser.add_argument(
        "--include-prop-targets",
        action="store_true",
        help="with --data-like-only, still probe declarations whose final arity sort is Prop",
    )
    parser.add_argument(
        "--include-prop-arguments",
        action="store_true",
        help="with --data-like-only, still probe declarations with Prop in explicit parameter types",
    )
    parser.add_argument(
        "--include-indexed-families",
        action="store_true",
        help="with --data-like-only, still probe declarations whose final arity still has non-sort arguments, e.g. bool -> Set",
    )
    parser.add_argument(
        "--include-non-sort-parameters",
        action="store_true",
        help="with --data-like-only, still probe declarations with explicit parameters whose type is not exactly Set or Type",
    )
    parser.add_argument(
        "--include-non-data-records",
        action="store_true",
        help="with --data-like-only, still probe records whose fields are not ordinary data fields, such as proof, Type-valued, function, or dependent fields",
    )
    return parser.parse_args()


def skip_reason(candidate: Candidate, args: argparse.Namespace) -> str | None:
    if not args.data_like_only:
        return None
    if candidate.target_sort == "Prop" and not args.include_prop_targets:
        return "prop-target"
    if candidate.has_prop_argument and not args.include_prop_arguments:
        return "prop-argument"
    if candidate.has_non_sort_parameter and not args.include_non_sort_parameters:
        return "non-sort-parameter"
    if candidate.record_data_issue and not args.include_non_data_records:
        return candidate.record_data_issue
    if candidate.has_indices and not args.include_indexed_families:
        return "indexed-family"
    return None


def main(args: argparse.Namespace) -> int:
    repo = args.repo.resolve()
    out_dir = (repo / args.out_dir).resolve() if not args.out_dir.is_absolute() else args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    if not args.skip_dune_build:
        print("Building rocq-json with dune build ...", flush=True)
        build = run(["dune", "build"], cwd=repo)
        (out_dir / "dune_build.log").write_text(build.stdout, encoding="utf-8")
        if build.returncode != 0:
            print(build.stdout)
            return build.returncode

    config = rocq_config(args.rocq)
    coqlib = Path(config["COQLIB"]).resolve()
    corelib = coqlib / "theories"
    stdlib = coqlib / "user-contrib" / "Stdlib"

    roots: list[tuple[str, Path]] = []
    if args.libraries in ("corelib", "both"):
        roots.append(("Corelib", corelib))
    if args.libraries in ("stdlib", "both"):
        roots.append(("Stdlib", stdlib))

    missing = [str(path) for _, path in roots if not path.exists()]
    if missing:
        print("Missing library source directories:")
        for path in missing:
            print(f"  {path}")
        return 2

    candidates: list[Candidate] = []
    for root_name, root in roots:
        candidates.extend(discover(root_name, root))
    if args.limit is not None:
        candidates = candidates[: args.limit]

    (out_dir / "discovered.json").write_text(
        json.dumps([asdict(candidate) | {"logical_name": candidate.logical_name} for candidate in candidates], indent=2),
        encoding="utf-8",
    )
    print(f"Discovered {len(candidates)} inductive-like declarations.", flush=True)

    skipped: list[tuple[Candidate, str]] = []
    probe_candidates: list[Candidate] = []
    for candidate in candidates:
        reason = skip_reason(candidate, args)
        if reason:
            skipped.append((candidate, reason))
        else:
            probe_candidates.append(candidate)

    (out_dir / "skipped_candidates.json").write_text(
        json.dumps([asdict(candidate) | {"logical_name": candidate.logical_name, "skip_reason": reason} for candidate, reason in skipped], indent=2),
        encoding="utf-8",
    )
    write_candidates_csv(out_dir / "skipped_candidates.csv", skipped)
    if skipped:
        skip_counts: dict[str, int] = {}
        for _candidate, reason in skipped:
            skip_counts[reason] = skip_counts.get(reason, 0) + 1
        print(f"Skipping {len(skipped)} declarations outside the default data-like fragment: {skip_counts}.", flush=True)

    rocq_json_root, derivers_root = detect_build_roots(repo)
    extra_args = rocq_args(repo, rocq_json_root, derivers_root)

    results: list[ProbeResult] = []
    successes: list[Candidate] = []
    for index, candidate in enumerate(probe_candidates, start=1):
        print(f"[{index}/{len(probe_candidates)}] probing {candidate.logical_name}", flush=True)
        result = probe_candidate(candidate, index, args.rocq, repo, out_dir, args.probe_timeout, extra_args)
        results.append(result)
        if result.status == "ok":
            successes.append(candidate)

    write_csv(out_dir / "probe_results.csv", results)
    (out_dir / "probe_results.json").write_text(
        json.dumps([asdict(result) for result in results], indent=2),
        encoding="utf-8",
    )
    write_failure_report(out_dir / "failures.md", results)

    bench_file = out_dir / "JsonifiableStdlibBenchmark.v"
    write_benchmark_file(bench_file, successes)

    print(f"Compiling benchmark artifact with {len(successes)} successful derivations ...", flush=True)
    cmd = [args.rocq, "c", *extra_args, str(bench_file)]
    start = time.perf_counter()
    compile_proc = run(cmd, cwd=repo)
    wall = time.perf_counter() - start
    compile_log = out_dir / "JsonifiableStdlibBenchmark.log"
    compile_log.write_text(compile_proc.stdout, encoding="utf-8")
    final_times = rocq_times(compile_proc.stdout)
    timing_rows = list(zip(successes, final_times))
    with (out_dir / "benchmark_timings.csv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "index",
                "library",
                "logical_name",
                "kind",
                "target_sort",
                "arity",
                "has_prop_argument",
                "has_indices",
                "has_non_sort_parameter",
                "has_untyped_parameter",
                "record_data_issue",
                "source",
                "line",
                "rocq_time_seconds",
            ],
        )
        writer.writeheader()
        for index, (candidate, seconds) in enumerate(timing_rows, start=1):
            writer.writerow(
                {
                    "index": index,
                    "library": candidate.library,
                    "logical_name": candidate.logical_name,
                    "kind": candidate.kind,
                    "target_sort": candidate.target_sort,
                    "arity": candidate.arity,
                    "has_prop_argument": candidate.has_prop_argument,
                    "has_indices": candidate.has_indices,
                    "has_non_sort_parameter": candidate.has_non_sort_parameter,
                    "has_untyped_parameter": candidate.has_untyped_parameter,
                    "record_data_issue": candidate.record_data_issue,
                    "source": candidate.source,
                    "line": candidate.line,
                    "rocq_time_seconds": seconds,
                }
            )

    ok = sum(1 for result in results if result.status == "ok")
    fail = sum(1 for result in results if result.status == "fail")
    timeout = sum(1 for result in results if result.status == "timeout")
    categories: dict[str, int] = {}
    for result in results:
        if result.status != "ok":
            categories[result.category] = categories.get(result.category, 0) + 1
    skip_categories: dict[str, int] = {}
    for _candidate, reason in skipped:
        skip_categories[reason] = skip_categories.get(reason, 0) + 1
    summary = {
        "coqlib": str(coqlib),
        "corelib_theories": str(corelib),
        "stdlib_theories": str(stdlib),
        "discovered": len(candidates),
        "skipped_prop_targets": skip_categories.get("prop-target", 0),
        "skipped_categories": skip_categories,
        "probed": len(probe_candidates),
        "probe_successes": ok,
        "probe_failures": fail,
        "probe_timeouts": timeout,
        "benchmark_file": str(bench_file),
        "benchmark_log": str(compile_log),
        "failure_report": str(out_dir / "failures.md"),
        "probe_logs_dir": str(out_dir / "probes"),
        "skipped_candidates": str(out_dir / "skipped_candidates.csv"),
        "failure_categories": categories,
        "benchmark_compile_status": compile_proc.returncode,
        "benchmark_wall_seconds": wall,
        "timed_derivations": len(final_times),
        "sum_rocq_time_seconds": sum(final_times),
        "min_rocq_time_seconds": min(final_times) if final_times else None,
        "max_rocq_time_seconds": max(final_times) if final_times else None,
        "mean_rocq_time_seconds": (sum(final_times) / len(final_times)) if final_times else None,
    }
    (out_dir / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")

    print(json.dumps(summary, indent=2))
    return compile_proc.returncode


if __name__ == "__main__":
    cli_args = parse_args()
    if not cli_args.skip_dune_build and shutil.which("dune") is None:
        print("error: dune is not on PATH", file=sys.stderr)
        sys.exit(127)
    sys.exit(main(cli_args))
