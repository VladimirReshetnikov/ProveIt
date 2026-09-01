#!/usr/bin/env python3
"""Rebuild and verify the historical source-result inventory.

The canonical concordance has reviewed editorial columns that text extraction
cannot reconstruct. This program therefore rebuilds only the immutable source
projection, normally from the commit pinned in ``SOURCE_REVISION``, and can
compare that projection with the reviewed concordance. It never overwrites the
canonical concordance.
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
    "researchproblem",
    "principle",
    "definition",
    "algorithm",
    "computationalresult",
    "example",
)

BEGIN_RE = re.compile(
    r"\\begin\{(?P<kind>" + "|".join(RESULT_KINDS) + r")\}"
    r"(?:\[(?P<title>.*?)\])?",
    re.DOTALL,
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
PROOF_RE = re.compile(r"\\begin\{(?:proof|proofidea)\}")
SECTION_RE = re.compile(
    r"\\(?P<level>part|chapter|section|subsection)\*?"
    r"\{(?P<title>.*?)\}",
    re.DOTALL,
)

AUDIT_DIR = Path(__file__).resolve().parent
CANONICAL_ROOT = AUDIT_DIR.parent
PIN_FILE = AUDIT_DIR / "SOURCE_REVISION"
CANONICAL_CONCORDANCE = CANONICAL_ROOT / "theorem_concordance.csv"
REPOSITORY_SOURCE_ROOT = Path(
    "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
    "drafts/exponents-and-q-series"
)

SOURCES = (
    (
        "inverse_q_analog_functions_report",
        "inverse_q_analog_functions_report/inverse_q_analog_functions.tex",
    ),
    (
        "inverse_q_analog_jet_atlas",
        "inverse_q_analog_jet_atlas/inverse_q_analog_jet_atlas.tex",
    ),
    (
        "inverse_q_analogs_extended_report",
        "inverse_q_analogs_extended_report/inverse_q_analogs_extended_report.tex",
    ),
    (
        "inverse_q_analogs_report",
        "inverse_q_analogs_report/inverse_q_analogs_report.tex",
    ),
    (
        "inverse_q_analogs_report-2",
        "inverse_q_analogs_report-2/inverse_q_analogs_report.tex",
    ),
    (
        "q_pochhammer_q_binomial_expansions_report",
        "q_pochhammer_q_binomial_expansions_report/q_analog_expansions_report.tex",
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
    """Collapse TeX layout whitespace without trying to interpret TeX."""

    return " ".join(text.split())


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def current_section(
    section_matches: list[re.Match[str]], result_offset: int
) -> tuple[str, str]:
    path: dict[str, str] = {}
    for match in section_matches:
        if match.start() >= result_offset:
            break
        level = match.group("level")
        path[level] = one_line(match.group("title"))
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
        path[key]
        for key in ("part", "chapter", "section", "subsection")
        if key in path
    ]
    return path.get("chapter", ""), " / ".join(ordered)


def inventory_text(
    text: str, package: str, relative: str, display_source: str
) -> list[dict[str, str]]:
    results = list(BEGIN_RE.finditer(text))
    sections = list(SECTION_RE.finditer(text))
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
            "source_title": one_line(match.group("title") or ""),
            "source_chapter": chapter,
            "source_section_path": section_path,
            "source_proof_present": "yes" if proof_present else "no",
        }
        row.update({field: "" for field in EDITORIAL_FIELDS})
        rows.append(row)
    return rows


def run_git(repo_root: Path, *arguments: str) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git {' '.join(arguments)} failed: {detail}")
    return completed.stdout


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


def resolve_revision(repo_root: Path, revision: str) -> str:
    resolved = run_git(repo_root, "rev-parse", "--verify", f"{revision}^{{commit}}")
    commit = resolved.decode("ascii").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise RuntimeError(f"git returned a noncanonical commit id: {commit!r}")
    return commit


def inventory_revision(revision: str) -> tuple[str, list[dict[str, str]]]:
    repo_root = repository_root()
    commit = resolve_revision(repo_root, revision)
    rows: list[dict[str, str]] = []
    for package, relative in SOURCES:
        repository_path = (REPOSITORY_SOURCE_ROOT / relative).as_posix()
        blob = run_git(repo_root, "show", f"{commit}:{repository_path}")
        text = blob.decode("utf-8")
        rows.extend(
            inventory_text(text, package, relative, f"{commit}:{repository_path}")
        )
    return commit, rows


def inventory_working_tree(source_root: Path) -> list[dict[str, str]]:
    root = source_root.resolve()
    rows: list[dict[str, str]] = []
    for package, relative in SOURCES:
        path = root / relative
        text = path.read_text(encoding="utf-8")
        rows.extend(inventory_text(text, package, relative, str(path)))
    return rows


def source_projection_sha256(rows: list[dict[str, str]]) -> str:
    stream = io.StringIO(newline="")
    writer = csv.DictWriter(
        stream, fieldnames=SOURCE_FIELDS, lineterminator="\n", extrasaction="ignore"
    )
    writer.writeheader()
    writer.writerows(rows)
    return hashlib.sha256(stream.getvalue().encode("utf-8")).hexdigest()


def write_inventory(path: Path, rows: list[dict[str, str]]) -> None:
    if path.resolve() == CANONICAL_CONCORDANCE.resolve():
        raise ValueError(
            "refusing to overwrite theorem_concordance.csv: it contains "
            "reviewed editorial dispositions"
        )
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=ALL_FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def concordance_mismatches(
    rows: list[dict[str, str]], concordance: Path
) -> list[str]:
    with concordance.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        reviewed = list(reader)
        fields = reader.fieldnames or []
    missing_fields = [field for field in SOURCE_FIELDS if field not in fields]
    if missing_fields:
        return ["concordance lacks source fields: " + ", ".join(missing_fields)]
    failures: list[str] = []
    if len(reviewed) != len(rows):
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
                if len(failures) >= 20:
                    failures.append("further mismatches suppressed")
                    return failures
    return failures


def print_summary(rows: list[dict[str, str]]) -> None:
    kinds = Counter(row["source_kind"] for row in rows)
    packages = Counter(row["source_package"] for row in rows)
    missing_proofs = sum(row["source_proof_present"] == "no" for row in rows)
    missing_labels = sum(not row["source_label"] for row in rows)

    print(f"result environments: {len(rows)}")
    print(f"source projection sha256: {source_projection_sha256(rows)}")
    print("by kind:")
    for kind, count in sorted(kinds.items()):
        print(f"  {kind:20s} {count:3d}")
    print("by package:")
    for package, count in sorted(packages.items()):
        print(f"  {package:45s} {count:3d}")
    print(f"without source labels: {missing_labels}")
    print(f"without an intervening proof environment: {missing_proofs}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    source = parser.add_mutually_exclusive_group()
    source.add_argument(
        "--source-revision",
        metavar="REV",
        help="Git commit containing the six source reports (default: SOURCE_REVISION)",
    )
    source.add_argument(
        "--source-root",
        type=Path,
        help="working-tree exponents-and-q-series directory (diagnostic only)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="write a raw inventory to this noncanonical CSV path",
    )
    parser.add_argument(
        "--verify-concordance",
        type=Path,
        metavar="CSV",
        help=(
            "compare the ten source columns with a reviewed concordance "
            "(default action: verify the canonical concordance)"
        ),
    )
    args = parser.parse_args()

    try:
        verify_path = args.verify_concordance
        if args.output is None and verify_path is None:
            verify_path = CANONICAL_CONCORDANCE

        if args.source_root is not None:
            rows = inventory_working_tree(args.source_root)
            print(f"source: working tree {args.source_root.resolve()}")
        else:
            revision = args.source_revision or PIN_FILE.read_text(encoding="utf-8").strip()
            commit, rows = inventory_revision(revision)
            print(f"source revision: {commit}")

        if args.output is not None:
            write_inventory(args.output, rows)
            print(f"wrote raw inventory: {args.output}")

        if verify_path is not None:
            failures = concordance_mismatches(rows, verify_path)
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
