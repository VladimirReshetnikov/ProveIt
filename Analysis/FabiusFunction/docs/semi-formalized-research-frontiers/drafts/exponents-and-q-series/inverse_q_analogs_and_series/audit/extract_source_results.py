#!/usr/bin/env python3
"""Build the source-result inventory for the inverse-q consolidation.

The six reports use several theorem-like environments and inconsistent label
coverage.  This script records every result environment, its enclosing
section, source line, label (when present), and whether a proof environment
occurs before the next result.  It deliberately leaves canonical disposition
fields blank: those require mathematical review rather than text matching.
"""

from __future__ import annotations

import argparse
import csv
import re
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
    ordered = [path[key] for key in ("part", "chapter", "section", "subsection")
               if key in path]
    return path.get("chapter", ""), " / ".join(ordered)


def inventory_source(source_root: Path, package: str, relative: str) -> list[dict[str, str]]:
    path = source_root / relative
    text = path.read_text(encoding="utf-8")
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
                f"{path}:{line_number(text, match.start())}: "
                f"missing {end_token}"
            )
        statement_end += len(end_token)
        next_start = results[index + 1].start() if index + 1 < len(results) else len(text)
        statement = text[match.end():statement_end]
        label_match = LABEL_RE.search(statement)
        label = label_match.group(1) if label_match else ""
        key = label or f"unlabelled-{kind}-{ordinals[kind]:03d}"
        chapter, section_path = current_section(sections, match.start())
        proof_present = bool(PROOF_RE.search(text[statement_end:next_start]))

        rows.append(
            {
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
                "canonical_label": "",
                "canonical_status": "",
                "lean_module": "",
                "lean_declaration": "",
                "disposition_notes": "",
            }
        )
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="CSV destination (defaults to the canonical package root)",
    )
    args = parser.parse_args()

    canonical_root = Path(__file__).resolve().parents[1]
    source_root = canonical_root.parent
    output = args.output or canonical_root / "theorem_concordance.csv"

    rows: list[dict[str, str]] = []
    for package, relative in SOURCES:
        rows.extend(inventory_source(source_root, package, relative))

    fieldnames = list(rows[0])
    with output.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)

    kinds = Counter(row["source_kind"] for row in rows)
    packages = Counter(row["source_package"] for row in rows)
    missing_proofs = sum(row["source_proof_present"] == "no" for row in rows)
    missing_labels = sum(not row["source_label"] for row in rows)

    print(f"wrote {len(rows)} result environments to {output}")
    print("by kind:")
    for kind, count in sorted(kinds.items()):
        print(f"  {kind:20s} {count:3d}")
    print("by package:")
    for package, count in sorted(packages.items()):
        print(f"  {package:45s} {count:3d}")
    print(f"without source labels: {missing_labels}")
    print(f"without an intervening proof environment: {missing_proofs}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
