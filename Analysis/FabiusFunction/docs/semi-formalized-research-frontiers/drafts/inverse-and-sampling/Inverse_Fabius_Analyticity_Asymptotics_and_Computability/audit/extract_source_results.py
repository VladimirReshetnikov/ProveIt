#!/usr/bin/env python3
"""Reproduce the immutable source-result projection for the canonical volume.

The reviewed concordance contains editorial fields that extraction cannot
infer.  This program therefore reconstructs only the source fields from the
commit pinned in ``SOURCE_REVISION`` and compares them with the canonical CSV.
It refuses to overwrite that reviewed CSV.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path


RESULT_KINDS = (
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "conjecture",
    "problem",
    "definition",
    "algorithm",
    "example",
    "obligation",
    "warning",
)
BEGIN_RE = re.compile(
    r"\\begin\{(?P<kind>" + "|".join(RESULT_KINDS) + r")\}"
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
PROOF_RE = re.compile(r"\\begin\{(?:proof|proofidea)\}")
SECTION_RE = re.compile(
    r"\\(?P<level>part|chapter|section|subsection)\*?\s*\{"
)

AUDIT_DIR = Path(__file__).resolve().parent
CANONICAL_ROOT = AUDIT_DIR.parent
PIN_FILE = AUDIT_DIR / "SOURCE_REVISION"
CANONICAL_CONCORDANCE = CANONICAL_ROOT / "theorem_concordance.csv"
REPOSITORY_SOURCE_ROOT = Path(
    "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
    "drafts/inverse-and-sampling"
)
SOURCES = (
    (
        "Inverse_and_Sampling_Frontiers",
        "inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers/"
        "Inverse_and_Sampling_Frontiers.tex",
    ),
    (
        "Inverse_Endpoint_All_Orders",
        "inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders/"
        "Inverse_Endpoint_All_Orders.tex",
    ),
    (
        "Inverse_Fabius_Computability_Report",
        "inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/"
        "inverse_fabius_computability.tex",
    ),
    (
        "Non_Elementarity_of_the_Fabius_Function",
        "analyticity-and-elementarity/Non_Elementarity_of_the_Fabius_Function/"
        "Non_Elementarity_of_the_Fabius_Function.tex",
    ),
    (
        "inverse_fabius_iterates_nowhere_analytic",
        "analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/"
        "inverse_fabius_iterates_nowhere_analytic.tex",
    ),
)
SOURCE_FIELDS = (
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
)
EDITORIAL_FIELDS = (
    "canonical_label",
    "canonical_status",
    "lean_module",
    "lean_declaration",
    "disposition_notes",
)
ALL_FIELDS = SOURCE_FIELDS + EDITORIAL_FIELDS


def one_line(text: str) -> str:
    return " ".join(text.split())


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def balanced_contents(
    text: str, opening: int, left: str, right: str, display_source: str
) -> tuple[str, int]:
    """Return a balanced TeX argument and the offset immediately after it.

    A non-greedy regular expression truncates a section title with nested
    braces at the first closing brace.  This deliberately small scanner is
    sufficient for ordinary TeX arguments: it respects nesting and ignores
    escaped delimiters.
    """

    if opening >= len(text) or text[opening] != left:
        raise ValueError(
            f"{display_source}:{line_number(text, opening)}: expected {left!r}"
        )
    depth = 1
    index = opening + 1
    while index < len(text):
        character = text[index]
        if character == "\\":
            index += 2
            continue
        if character == left:
            depth += 1
        elif character == right:
            depth -= 1
            if depth == 0:
                return text[opening + 1 : index], index + 1
        index += 1
    raise ValueError(
        f"{display_source}:{line_number(text, opening)}: "
        f"unclosed balanced argument beginning with {left!r}"
    )


def result_title(text: str, offset: int, display_source: str) -> str:
    index = offset
    while index < len(text) and text[index].isspace():
        index += 1
    if index < len(text) and text[index] == "[":
        title, _ = balanced_contents(text, index, "[", "]", display_source)
        return one_line(title)
    return ""


def section_marks(text: str, display_source: str) -> list[tuple[int, str, str]]:
    marks: list[tuple[int, str, str]] = []
    for match in SECTION_RE.finditer(text):
        title, _ = balanced_contents(
            text, match.end() - 1, "{", "}", display_source
        )
        marks.append((match.start(), match.group("level"), one_line(title)))
    return marks


def current_section(
    marks: list[tuple[int, str, str]], offset: int
) -> tuple[str, str]:
    path: dict[str, str] = {}
    for start, level, title in marks:
        if start >= offset:
            break
        path[level] = title
        if level == "part":
            path.pop("chapter", None)
            path.pop("section", None)
            path.pop("subsection", None)
        elif level == "chapter":
            path.pop("section", None)
            path.pop("subsection", None)
        elif level == "section":
            path.pop("subsection", None)
    ordered = [
        path[level]
        for level in ("part", "chapter", "section", "subsection")
        if level in path
    ]
    return path.get("chapter", ""), " / ".join(ordered)


def inventory_text(
    text: str, package: str, relative: str, display_source: str
) -> list[dict[str, str]]:
    results = list(BEGIN_RE.finditer(text))
    sections = section_marks(text, display_source)
    ordinals: Counter[str] = Counter()
    rows: list[dict[str, str]] = []
    for index, match in enumerate(results):
        kind = match.group("kind")
        ordinals[kind] += 1
        end_token = rf"\end{{{kind}}}"
        statement_end = text.find(end_token, match.end())
        if statement_end < 0:
            raise ValueError(
                f"{display_source}:{line_number(text, match.start())}: "
                f"missing {end_token}"
            )
        statement_end += len(end_token)
        next_start = (
            results[index + 1].start() if index + 1 < len(results) else len(text)
        )
        statement = text[match.end() : statement_end]
        label_match = LABEL_RE.search(statement)
        label = label_match.group(1) if label_match else ""
        key = label or f"unlabelled-{kind}-{ordinals[kind]:03d}"
        chapter, section_path = current_section(sections, match.start())
        proof_present = bool(PROOF_RE.search(text[statement_end:next_start]))
        row = {
            "source_key": f"{package}:{key}",
            "source_package": package,
            "source_file": relative.replace("\\", "/"),
            "source_line": str(line_number(text, match.start())),
            "source_label": label,
            "source_kind": kind,
            "source_title": result_title(text, match.end(), display_source),
            "source_chapter": chapter,
            "source_section_path": section_path,
            "source_proof_present": "yes" if proof_present else "no",
        }
        row.update({field: "" for field in EDITORIAL_FIELDS})
        rows.append(row)
    return rows


def repository_root() -> Path:
    completed = subprocess.run(
        ["git", "-C", str(CANONICAL_ROOT), "rev-parse", "--show-toplevel"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"cannot locate repository root: {detail}")
    return Path(completed.stdout.decode("utf-8").strip()).resolve()


def run_git(repo: Path, *arguments: str) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(repo), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git {' '.join(arguments)} failed: {detail}")
    return completed.stdout


def inventory_revision(revision: str) -> tuple[str, list[dict[str, str]]]:
    repo = repository_root()
    resolved = run_git(repo, "rev-parse", "--verify", f"{revision}^{{commit}}")
    commit = resolved.decode("ascii").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise RuntimeError(f"noncanonical commit id: {commit!r}")
    rows: list[dict[str, str]] = []
    for package, relative in SOURCES:
        repository_path = (REPOSITORY_SOURCE_ROOT / relative).as_posix()
        blob = run_git(repo, "show", f"{commit}:{repository_path}")
        rows.extend(
            inventory_text(
                blob.decode("utf-8"),
                package,
                relative,
                f"{commit}:{repository_path}",
            )
        )
    return commit, rows


def projection_sha256(rows: list[dict[str, str]]) -> str:
    stream = io.StringIO(newline="")
    writer = csv.DictWriter(
        stream,
        fieldnames=SOURCE_FIELDS,
        extrasaction="ignore",
        lineterminator="\n",
    )
    writer.writeheader()
    writer.writerows(rows)
    return hashlib.sha256(stream.getvalue().encode("utf-8")).hexdigest()


def write_inventory(path: Path, rows: list[dict[str, str]]) -> None:
    if path.resolve() == CANONICAL_CONCORDANCE.resolve():
        raise ValueError(
            "refusing to overwrite theorem_concordance.csv; it contains "
            "reviewed editorial dispositions"
        )
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=ALL_FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def concordance_mismatches(
    rows: list[dict[str, str]], path: Path
) -> list[str]:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        reviewed = list(reader)
        fields = reader.fieldnames or []
    missing = [field for field in SOURCE_FIELDS if field not in fields]
    if missing:
        return ["concordance lacks source fields: " + ", ".join(missing)]
    failures: list[str] = []
    if len(rows) != len(reviewed):
        failures.append(
            f"row count differs: extracted={len(rows)}, concordance={len(reviewed)}"
        )
    for index, (extracted, retained) in enumerate(zip(rows, reviewed), start=2):
        for field in SOURCE_FIELDS:
            if extracted[field] != retained[field]:
                failures.append(
                    f"CSV row {index} {field}: extracted={extracted[field]!r}, "
                    f"concordance={retained[field]!r}"
                )
                if len(failures) == 20:
                    failures.append("further mismatches suppressed")
                    return failures
    return failures


def print_summary(rows: list[dict[str, str]]) -> None:
    kinds = Counter(row["source_kind"] for row in rows)
    packages = Counter(row["source_package"] for row in rows)
    print(f"result environments: {len(rows)}")
    print(f"source projection sha256: {projection_sha256(rows)}")
    print("by kind:")
    for kind, count in sorted(kinds.items()):
        print(f"  {kind:16s} {count:3d}")
    print("by package:")
    for package, count in sorted(packages.items()):
        print(f"  {package:42s} {count:3d}")
    print(f"without source labels: {sum(not row['source_label'] for row in rows)}")
    print(
        "without an intervening proof environment: "
        f"{sum(row['source_proof_present'] == 'no' for row in rows)}"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--source-revision", metavar="REV")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-concordance", type=Path, metavar="CSV")
    args = parser.parse_args()
    try:
        revision = args.source_revision or PIN_FILE.read_text(encoding="utf-8").strip()
        commit, rows = inventory_revision(revision)
        print(f"source revision: {commit}")
        if args.output is not None:
            write_inventory(args.output, rows)
            print(f"wrote raw inventory: {args.output}")
        verify = args.verify_concordance
        if args.output is None and verify is None:
            verify = CANONICAL_CONCORDANCE
        if verify is not None:
            failures = concordance_mismatches(rows, verify)
            if failures:
                print("source-concordance verification FAILED", file=sys.stderr)
                for failure in failures:
                    print(f"- {failure}", file=sys.stderr)
                return 1
            print(
                "source-concordance verification: PASS "
                f"({len(rows)} rows x {len(SOURCE_FIELDS)} fields)"
            )
        print_summary(rows)
        if args.output is None:
            print("no CSV written")
        return 0
    except (OSError, UnicodeError, ValueError, RuntimeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
