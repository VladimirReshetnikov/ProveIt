#!/usr/bin/env python3
"""Static publication and coverage gate for the canonical inverse-q volume.

This checker deliberately avoids TeX expansion.  It verifies the structural
invariants that are easy to lose during a large editorial consolidation;
pdfLaTeX and rendered-page inspection remain separate publication gates.
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from collections import Counter
from pathlib import Path

from extract_source_results import (
    SOURCE_FIELDS,
    concordance_mismatches,
    inventory_revision,
)


PACKAGE = Path(__file__).resolve().parents[1]
MASTER = PACKAGE / "inverse_q_analogs_and_series.tex"
CHAPTER_DIR = PACKAGE / "chapters"
CONCORDANCE = PACKAGE / "theorem_concordance.csv"
SOURCE_REVISION = PACKAGE / "audit" / "SOURCE_REVISION"

RESULT_ENVS = {
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "conjecture",
    "definition",
    "algorithm",
    "example",
}
PROVED_ENVS = {"theorem", "proposition", "lemma", "corollary"}
ASSERTION_KINDS = PROVED_ENVS | {"conjecture", "problem", "researchproblem"}
CANONICAL_STATUSES = {
    "Lean-proved",
    "human-proved frontier result",
    "conjecture",
    "not applicable",
}
CONCORDANCE_FIELDS = [
    "source_key",
    "source_package",
    "source_file",
    "source_line",
    "source_label",
    "source_kind",
    "source_title",
    "source_chapter",
    "source_section_path",
    "source_proof_present",
    "canonical_label",
    "canonical_status",
    "lean_module",
    "lean_declaration",
    "disposition_notes",
]
FORBIDDEN = (
    "TODO",
    "FIXME",
    "pending synthesis",
    "CHAPTER06_CONTINUE",
    "<<<<<<<",
    "=======",
    ">>>>>>>",
)

BEGIN_END_RE = re.compile(r"\\(begin|end)\{([^}]+)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
REF_RE = re.compile(r"\\(?:[cC]ref|ref|eqref)\{([^}]+)\}")
INPUT_RE = re.compile(r"\\input\{([^}]+)\}")
COMMENT_RE = re.compile(r"(?<!\\)%.*$")


def without_comments(text: str) -> str:
    return "\n".join(COMMENT_RE.sub("", line) for line in text.splitlines())


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def check_environment_stack(path: Path, text: str, failures: list[str]) -> None:
    stack: list[tuple[str, int]] = []
    for match in BEGIN_END_RE.finditer(without_comments(text)):
        direction, name = match.groups()
        line = line_of(text, match.start())
        if direction == "begin":
            stack.append((name, line))
            continue
        if not stack:
            failures.append(f"{path.name}:{line}: unmatched \\end{{{name}}}")
            continue
        open_name, open_line = stack.pop()
        if open_name != name:
            failures.append(
                f"{path.name}:{line}: \\end{{{name}}} closes "
                f"\\begin{{{open_name}}} from line {open_line}"
            )
    for name, line in stack:
        failures.append(f"{path.name}:{line}: unclosed \\begin{{{name}}}")


def result_blocks(text: str) -> list[tuple[str, int, int, int]]:
    """Return (environment, begin, end, line) for top-level result blocks."""
    clean = without_comments(text)
    matches = list(BEGIN_END_RE.finditer(clean))
    stack: list[tuple[str, int, int]] = []
    blocks: list[tuple[str, int, int, int]] = []
    for match in matches:
        direction, name = match.groups()
        if direction == "begin":
            stack.append((name, match.start(), line_of(clean, match.start())))
            continue
        if not stack:
            continue
        open_name, begin, line = stack.pop()
        if open_name == name and name in RESULT_ENVS:
            blocks.append((name, begin, match.end(), line))
    return sorted(blocks, key=lambda item: item[1])


def check_proof_coverage(path: Path, text: str, failures: list[str]) -> Counter[str]:
    blocks = result_blocks(text)
    counts = Counter(name for name, *_ in blocks)
    clean = without_comments(text)
    for index, (name, _begin, end, line) in enumerate(blocks):
        if name not in PROVED_ENVS:
            continue
        next_begin = blocks[index + 1][1] if index + 1 < len(blocks) else len(clean)
        between = clean[end:next_begin]
        if r"\begin{proof}" not in between:
            failures.append(
                f"{path.name}:{line}: {name} has no proof before the next result"
            )
    return counts


def check_master_inputs(failures: list[str]) -> list[Path]:
    master_text = MASTER.read_text(encoding="utf-8")
    chapter_paths: list[Path] = []
    chapter_dir = CHAPTER_DIR.resolve()
    for relative in INPUT_RE.findall(without_comments(master_text)):
        input_path = Path(relative)
        if input_path.suffix != ".tex":
            input_path = input_path.with_suffix(".tex")
        path = (PACKAGE / input_path).resolve()
        if not path.is_file():
            failures.append(f"master input does not exist: {input_path.as_posix()}")
        elif path.parent == chapter_dir:
            chapter_paths.append(path)
    disk_chapters = sorted(CHAPTER_DIR.glob("*.tex"))
    if set(chapter_paths) != set(disk_chapters):
        missing = sorted(set(disk_chapters) - set(chapter_paths))
        extra = sorted(set(chapter_paths) - set(disk_chapters))
        if missing:
            failures.append(
                "chapters omitted by master: " + ", ".join(path.name for path in missing)
            )
        if extra:
            failures.append(
                "master inputs outside chapter inventory: "
                + ", ".join(path.name for path in extra)
            )
    return chapter_paths


def check_labels_and_refs(
    texts: list[tuple[Path, str]], failures: list[str]
) -> tuple[set[str], int]:
    label_locations: dict[str, list[str]] = {}
    references: list[tuple[str, str]] = []
    for path, text in texts:
        clean = without_comments(text)
        for match in LABEL_RE.finditer(clean):
            label_locations.setdefault(match.group(1), []).append(
                f"{path.name}:{line_of(clean, match.start())}"
            )
        for match in REF_RE.finditer(clean):
            for label in match.group(1).split(","):
                references.append(
                    (label.strip(), f"{path.name}:{line_of(clean, match.start())}")
                )
    for label, locations in sorted(label_locations.items()):
        if len(locations) > 1:
            failures.append(f"duplicate label {label}: {', '.join(locations)}")
    for label, location in references:
        if label and label not in label_locations:
            failures.append(f"{location}: unresolved reference {label}")
    return set(label_locations), len(references)


def check_concordance(
    allow_incomplete: bool, canonical_labels: set[str], failures: list[str]
) -> tuple[int, Counter[str], int]:
    with CONCORDANCE.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        rows = list(reader)
    if reader.fieldnames != CONCORDANCE_FIELDS:
        failures.append(
            "concordance header differs from the canonical schema: "
            + repr(reader.fieldnames)
        )
    if len(rows) != 260:
        failures.append(f"concordance has {len(rows)} rows, expected 260")
    keys = [row["source_key"] for row in rows]
    duplicates = [key for key, count in Counter(keys).items() if count > 1]
    if duplicates:
        failures.append("duplicate concordance source keys: " + ", ".join(duplicates))
    incomplete = [
        row["source_key"]
        for row in rows
        if not row["canonical_status"].strip() or not row["disposition_notes"].strip()
    ]
    if incomplete and not allow_incomplete:
        preview = ", ".join(incomplete[:5])
        failures.append(
            f"{len(incomplete)} concordance rows lack status/disposition"
            + (f" (first: {preview})" if preview else "")
        )
    for row in rows:
        key = row["source_key"]
        kind = row["source_kind"].strip()
        label = row["canonical_label"].strip()
        status = row["canonical_status"].strip()
        lean_module = row["lean_module"].strip()
        lean_declaration = row["lean_declaration"].strip()
        if status and status not in CANONICAL_STATUSES:
            failures.append(f"{key}: unknown canonical status {status!r}")
        if label and label not in canonical_labels:
            failures.append(f"{key}: unknown canonical label {label}")
        if status in {"Lean-proved", "human-proved frontier result", "conjecture"}:
            if not label:
                failures.append(f"{key}: retained assertion has no canonical label")
        if kind in ASSERTION_KINDS and status in {
            "Lean-proved",
            "human-proved frontier result",
            "conjecture",
        } and not label:
            failures.append(f"{key}: retained source assertion has no destination")
        if status == "conjecture" and label and not label.startswith("conj:"):
            failures.append(f"{key}: conjecture maps to non-conjecture label {label}")
        if status in {"Lean-proved", "human-proved frontier result"} and label.startswith(
            "conj:"
        ):
            failures.append(f"{key}: proved status maps to conjecture label {label}")
        if bool(lean_module) != bool(lean_declaration):
            failures.append(f"{key}: Lean module/declaration must be populated together")
        if status == "Lean-proved" and not (lean_module and lean_declaration):
            failures.append(f"{key}: Lean-proved status lacks an exact declaration")
        if lean_module and status != "Lean-proved":
            failures.append(f"{key}: exact Lean declaration requires Lean-proved status")
    return len(rows), Counter(row["source_kind"] for row in rows), len(incomplete)


def check_source_snapshot(failures: list[str]) -> tuple[str, int]:
    """Reproduce immutable source columns from the pinned historical tree."""

    try:
        revision = SOURCE_REVISION.read_text(encoding="utf-8").strip()
        if not revision:
            raise ValueError("SOURCE_REVISION is empty")
        commit, rows = inventory_revision(revision)
        mismatches = concordance_mismatches(rows, CONCORDANCE)
        failures.extend(f"source snapshot: {message}" for message in mismatches)
        return commit, len(rows)
    except (OSError, UnicodeError, ValueError, RuntimeError) as error:
        failures.append(
            "cannot reproduce pinned source snapshot "
            f"(fetch repository history if the clone is shallow): {error}"
        )
        return "unresolved", 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--allow-incomplete-concordance",
        action="store_true",
        help="report blank disposition rows without failing (development only)",
    )
    args = parser.parse_args()

    failures: list[str] = []
    chapter_paths = check_master_inputs(failures)
    paths = [MASTER, *chapter_paths]
    texts = [(path, path.read_text(encoding="utf-8")) for path in paths]

    result_counts: Counter[str] = Counter()
    for path, text in texts:
        check_environment_stack(path, text, failures)
        result_counts.update(check_proof_coverage(path, text, failures))
        for marker in FORBIDDEN:
            if marker in text:
                failures.append(f"{path.name}: forbidden construction marker {marker!r}")

    canonical_labels, ref_count = check_labels_and_refs(texts, failures)
    source_commit, reproduced_rows = check_source_snapshot(failures)
    row_count, source_counts, incomplete = check_concordance(
        args.allow_incomplete_concordance, canonical_labels, failures
    )

    print(f"master: {MASTER.name}")
    print(f"chapters: {len(chapter_paths)}")
    print(f"labels/references: {len(canonical_labels)}/{ref_count}")
    print(
        "canonical results: "
        + ", ".join(f"{kind}={result_counts[kind]}" for kind in sorted(result_counts))
    )
    print(
        f"source concordance: rows={row_count}, incomplete={incomplete}; "
        + ", ".join(f"{kind}={source_counts[kind]}" for kind in sorted(source_counts))
    )
    print(
        "source snapshot: "
        f"revision={source_commit}, rows={reproduced_rows}, "
        f"immutable-fields={len(SOURCE_FIELDS)}"
    )
    if failures:
        print("\nFAILED", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1
    print("\nPASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
