#!/usr/bin/env python3
"""Reproduce the theorem-style inventory of the four pinned manuscripts."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import re
import subprocess
from collections import Counter
from pathlib import Path


PACKAGE = Path(__file__).resolve().parents[1]
PIN = PACKAGE / "audit" / "SOURCE_REVISION"
CONCORDANCE = PACKAGE / "theorem_concordance.csv"
SOURCE_ROOT = Path(
    "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
    "drafts/inverse-and-sampling/comb-interpolation"
)
SOURCES = (
    ("dyadic", "Dyadic_Comb_Frontiers/Dyadic_Comb_Frontiers.tex"),
    (
        "geometric",
        "geometric_comb_interpolation_report/geometric_comb_interpolation_report.tex",
    ),
    (
        "geometric_3",
        "geometric_comb_interpolation_report-3/geometric_comb_interpolation.tex",
    ),
    (
        "geometric_q_fabius",
        "geometric_comb_q_fabius_report/geometric_comb_q_fabius_report.tex",
    ),
)
RESULT_KINDS = (
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "identity",
    "conjecture",
    "problem",
    "question",
    "definition",
    "algorithm",
    "example",
    "observation",
)
BEGIN_RE = re.compile(
    r"\\begin\{(?P<kind>" + "|".join(RESULT_KINDS) + r")\}"
    r"(?:\[(?P<title>.*?)\])?",
    re.DOTALL,
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
PROOF_RE = re.compile(r"\\begin\{proof\}")
SECTION_RE = re.compile(
    r"\\(?P<level>part|chapter|section|subsection)\*?\{(?P<title>.*?)\}",
    re.DOTALL,
)
SOURCE_FIELDS = (
    "source_key",
    "source_package",
    "source_file",
    "source_line",
    "source_label",
    "source_kind",
    "source_title",
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


def git(*arguments: str) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(PACKAGE), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git {' '.join(arguments)} failed: {detail}")
    return completed.stdout


def one_line(text: str) -> str:
    return " ".join(text.split())


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def section_path(matches: list[re.Match[str]], offset: int) -> str:
    path: dict[str, str] = {}
    for match in matches:
        if match.start() >= offset:
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
    return " / ".join(
        path[key] for key in ("part", "chapter", "section", "subsection") if key in path
    )


def inventory_text(text: str, package: str, relative: str) -> list[dict[str, str]]:
    results = list(BEGIN_RE.finditer(text))
    sections = list(SECTION_RE.finditer(text))
    ordinals: Counter[str] = Counter()
    rows: list[dict[str, str]] = []
    for index, match in enumerate(results):
        kind = match.group("kind")
        ordinals[kind] += 1
        end_token = rf"\end{{{kind}}}"
        end = text.find(end_token, match.end())
        if end < 0:
            raise ValueError(f"{relative}:{line_number(text, match.start())}: missing {end_token}")
        end += len(end_token)
        next_start = results[index + 1].start() if index + 1 < len(results) else len(text)
        statement = text[match.end() : end]
        label_match = LABEL_RE.search(statement)
        label = label_match.group(1) if label_match else ""
        key = label or f"unlabelled-{kind}-{ordinals[kind]:03d}"
        row = {
            "source_key": f"{package}:{key}",
            "source_package": package,
            "source_file": relative,
            "source_line": str(line_number(text, match.start())),
            "source_label": label,
            "source_kind": kind,
            "source_title": one_line(match.group("title") or ""),
            "source_section_path": section_path(sections, match.start()),
            "source_proof_present": "yes" if PROOF_RE.search(text[end:next_start]) else "no",
        }
        row.update({field: "" for field in EDITORIAL_FIELDS})
        rows.append(row)
    return rows


def inventory_revision(revision: str) -> tuple[str, list[dict[str, str]]]:
    commit = git("rev-parse", "--verify", f"{revision}^{{commit}}").decode().strip()
    rows: list[dict[str, str]] = []
    for package, relative in SOURCES:
        path = (SOURCE_ROOT / relative).as_posix()
        text = git("show", f"{commit}:{path}").decode("utf-8")
        rows.extend(inventory_text(text, package, relative))
    return commit, rows


def projection_sha256(rows: list[dict[str, str]]) -> str:
    stream = io.StringIO(newline="")
    writer = csv.DictWriter(
        stream,
        fieldnames=SOURCE_FIELDS,
        lineterminator="\n",
        extrasaction="ignore",
    )
    writer.writeheader()
    writer.writerows(rows)
    return hashlib.sha256(stream.getvalue().encode("utf-8")).hexdigest()


def mismatches(rows: list[dict[str, str]], concordance: Path) -> list[str]:
    with concordance.open(newline="", encoding="utf-8") as stream:
        reviewed = list(csv.DictReader(stream))
    failures: list[str] = []
    if len(rows) != len(reviewed):
        failures.append(f"row count differs: extracted={len(rows)}, reviewed={len(reviewed)}")
    for number, (source, retained) in enumerate(zip(rows, reviewed), start=2):
        for field in SOURCE_FIELDS:
            if source[field] != retained.get(field, ""):
                failures.append(
                    f"row {number} {field}: extracted={source[field]!r}, reviewed={retained.get(field)!r}"
                )
                if len(failures) == 20:
                    failures.append("further mismatches suppressed")
                    return failures
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-concordance", type=Path)
    parser.add_argument("--source-revision")
    args = parser.parse_args()
    revision = args.source_revision or PIN.read_text(encoding="utf-8").strip()
    commit, rows = inventory_revision(revision)
    if args.output:
        if args.output.resolve() == CONCORDANCE.resolve():
            raise ValueError("refusing to overwrite the reviewed canonical concordance")
        with args.output.open("w", encoding="utf-8", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=ALL_FIELDS, lineterminator="\n")
            writer.writeheader()
            writer.writerows(rows)
        print(f"wrote: {args.output}")
    verify = args.verify_concordance or (CONCORDANCE if not args.output else None)
    if verify:
        failures = mismatches(rows, verify)
        if failures:
            for failure in failures:
                print(f"FAILED: {failure}")
            return 1
        print(f"source-concordance verification: PASS ({len(rows)} rows)")
    print(f"source revision: {commit}")
    print(f"result environments: {len(rows)}")
    print(f"source projection sha256: {projection_sha256(rows)}")
    for key, count in sorted(Counter(row["source_kind"] for row in rows).items()):
        print(f"  {key}: {count}")
    for key, count in sorted(Counter(row["source_package"] for row in rows).items()):
        print(f"  {key}: {count}")
    print(f"without source labels: {sum(not row['source_label'] for row in rows)}")
    print(f"without explicit following proof: {sum(row['source_proof_present'] == 'no' for row in rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
