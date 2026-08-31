#!/usr/bin/env python3
"""Audit canonical notation across active FabiusFunction TeX sources.

The audit is deliberately lexical.  It gives a reproducible inventory over
every ``*.tex`` file below ``docs/`` except ``docs/archive/`` and detects the
high-risk aliases and overloads retired by ``docs/fabius-notation.tex``.
It does not attempt to parse TeX or decide the meaning of arbitrary one-letter
variables; those are documented by the catalogue's per-document namespace.

Default mode prints the inventory and finding counts but exits successfully;
use ``--list`` to print the individual findings.
``--strict`` turns findings into a failing CI-style gate.  ``--json`` emits the
same information as machine-readable JSON.  Paths may be supplied explicitly
for focused migration work; explicit archive paths are still rejected.

Examples::

    python Analysis/FabiusFunction/scripts/tex_notation_audit.py
    python Analysis/FabiusFunction/scripts/tex_notation_audit.py --strict
    python Analysis/FabiusFunction/scripts/tex_notation_audit.py --json report.json
    python Analysis/FabiusFunction/scripts/tex_notation_audit.py Analysis/FabiusFunction/docs/foo.tex
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Iterable


CANONICAL_INPUT = "fabius-notation.tex"

# Commands whose old names either hide semantics or have incompatible
# definitions in the active corpus.  The replacement column is intentionally
# explicit, even when the old rendering happened to be typographically equal.
RETIRED_COMMANDS = {
    "R": "RealNumbers",
    "C": "ComplexNumbers",
    "Q": "RationalNumbers",
    "N": "NaturalNumbers or PositiveIntegers",
    "Z": "IntegerNumbers",
    "Up": "RvachevUp",
    "up": "RvachevUp",
    "upf": "RvachevUp",
    "sinc": "SincRad or SincPi",
    "sincpi": "SincPi",
    "sincp": "SincPi",
    "sincpiPartc": "SincPi",
    "sincPartx": "SincRad",
    "sincPartl": "SincRad",
    "sincPartii": "SincRad",
    "sincPartxx": "SincRad",
    "sincPartll": "SincRad",
    "sincPartcc": "SincRad",
    "sincPartvvv": "SincRad",
    "wt": "BinaryDigitSum",
    "tm": "ThueMorseSignSymbol or ThueMorseSign",
    "TM": "ThueMorseSignSymbol or ThueMorseSign",
    "e": "EulerE",
    "ee": "EulerE",
    "ii": "ImaginaryUnit",
    "dd": "Differential",
    "Li": "Polylogarithm",
    "Var": "Variance",
    "Cov": "Covariance",
    "E": "Expectation",
    "Prob": "Probability",
    "Pp": "Probability",
    "bigO": "BigO or BigOAt",
    "Oh": "BigO or BigOAt",
    "smallo": "LittleO or LittleOAt",
    "littleo": "LittleO or LittleOAt",
    "littleoh": "LittleO or LittleOAt",
    "supp": "SupportOperator or SupportOf",
    "sgn": "Sign",
    "lcm": "LeastCommonMultiple",
    "ord": "OrderOperator",
    "TV": "TotalVariationOf or TotalVariationDistance",
    "dist": "MetricDistance or EqualInLaw",
    "vtwo": "TwoAdicValuation",
    "qbinom": "GaussianBinomial (three explicit arguments)",
    "qpoch": "QPochhammer (three explicit arguments)",
    "poch": "QPochhammer (three explicit arguments)",
    "Law": "LawOperator or LawOf",
    "Lop": "LaplaceTransformSymbol or LaplaceTransformOf",
    "abs": "AbsoluteValue",
    "norm": "Norm",
    "floor": "Floor",
    "ceil": "Ceiling",
    "pospart": "PositivePart",
    "set": "SetOf",
    "angles": "InnerProduct",
    "diag": "DiagonalOperator",
    "Span": "SpanOperator",
    "spanop": "SpanOperator",
    "Tr": "TraceOperator",
    "rank": "RankOperator",
    "Res": "ResidueOperator",
    "Id": "IdentityOperator",
    "Log": "PrincipalLogarithm",
    "defeq": "DefinitionEquals",
    "Fglobal": "FabiusGlobal",
    "Fs": "FabiusGlobal",
    "extF": "FabiusGlobal",
    "Fext": "FabiusGlobal",
    "InvF": "FabiusClampedQuantile or FabiusQuantile",
}

SEMANTIC_COMMANDS = {
    "FabiusBounded", "FabiusGlobal", "FabiusQuantile",
    "FabiusClampedQuantile", "RvachevUp", "SincRad", "SincPi",
    "FourierTwoPiOperator", "FourierAngularOperator",
    "FourierTwoPiTransformOf", "FourierAngularTransformOf",
    "FourierTwoPi", "FourierAngular", "LaplaceTransformOf",
    "MellinTransformOf", "BinaryDigitSum", "ThueMorseSign",
    "GaussianBinomial", "QPochhammer", "QInteger", "MetricDistance",
    "EqualInLaw", "ConvergesInLaw", "DyadicSigmaField",
    "DecayOptimizationObjective", "LinearizedDecayObjective",
}

DECL_RE = re.compile(
    r"\\(?:newcommand|renewcommand|providecommand)\*?\s*"
    r"(?:\{\s*)?\\(?P<name>[A-Za-z@]+)"
)
DECLARE_OPERATOR_RE = re.compile(
    r"\\DeclareMathOperator\*?\s*(?:\{\s*)?\\(?P<name>[A-Za-z@]+)"
)
COMMAND_RE = re.compile(r"\\(?P<name>[A-Za-z@]+)")
DOCUMENTCLASS_RE = re.compile(r"(?m)^[^%\n]*\\documentclass(?:\[[^]]*\])?\{")
INPUT_RE = re.compile(r"\\(?:input|include)\s*\{([^}]+)\}")


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    code: str
    message: str


def repository_paths() -> tuple[Path, Path, Path]:
    script = Path(__file__).resolve()
    fabius = script.parent.parent
    docs = fabius / "docs"
    archive = docs / "archive"
    return fabius, docs, archive


def is_under(path: Path, parent: Path) -> bool:
    try:
        path.resolve().relative_to(parent.resolve())
        return True
    except ValueError:
        return False


def active_tex_files(arguments: list[str], docs: Path, archive: Path) -> list[Path]:
    if not arguments:
        return sorted(
            path for path in docs.rglob("*.tex")
            if not is_under(path, archive)
        )

    files: set[Path] = set()
    for raw in arguments:
        path = Path(raw).resolve()
        if not path.exists():
            raise FileNotFoundError(raw)
        if is_under(path, archive):
            raise ValueError(f"archive is excluded: {path}")
        candidates = path.rglob("*.tex") if path.is_dir() else [path]
        for candidate in candidates:
            candidate = candidate.resolve()
            if candidate.suffix.lower() != ".tex":
                continue
            if not is_under(candidate, docs):
                raise ValueError(f"outside docs tree: {candidate}")
            if is_under(candidate, archive):
                # Parent-directory audits omit the archive just like the
                # default whole-corpus scan.  Explicit archive arguments were
                # rejected above.
                continue
            files.add(candidate)
    return sorted(files)


def strip_comments(text: str) -> str:
    """Replace unescaped TeX comments with spaces, preserving line numbers."""
    output: list[str] = []
    for line in text.splitlines(keepends=True):
        comment = None
        for index, char in enumerate(line):
            if char != "%":
                continue
            backslashes = 0
            cursor = index - 1
            while cursor >= 0 and line[cursor] == "\\":
                backslashes += 1
                cursor -= 1
            if backslashes % 2 == 0:
                comment = index
                break
        if comment is None:
            output.append(line)
        else:
            newline = "\n" if line.endswith("\n") else ""
            output.append(line[:comment] + " " * (len(line.rstrip("\n")) - comment) + newline)
    return "".join(output)


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def relative(path: Path, docs: Path) -> str:
    return path.relative_to(docs).as_posix()


def input_targets(text: str) -> list[str]:
    return [match.group(1).strip() for match in INPUT_RE.finditer(text)]


def audit_file(path: Path, docs: Path) -> tuple[dict, list[Finding], Counter[str]]:
    raw = path.read_text(encoding="utf-8-sig")
    code = strip_comments(raw)
    rel = relative(path, docs)
    canonical_source = rel == CANONICAL_INPUT
    root = bool(DOCUMENTCLASS_RE.search(code))
    findings: list[Finding] = []
    commands = Counter(match.group("name") for match in COMMAND_RE.finditer(code))

    canonical_mentions = sum(
        1 for target in input_targets(code)
        if Path(target).name == CANONICAL_INPUT
    )
    if root and canonical_mentions != 1:
        findings.append(Finding(
            rel, 1, "canonical-input-count",
            f"standalone document imports {CANONICAL_INPUT} {canonical_mentions} times; expected exactly once",
        ))
    if not root and canonical_mentions:
        findings.append(Finding(
            rel, 1, "fragment-import",
            "included fragments must inherit the canonical input from their standalone root",
        ))

    if not canonical_source:
        for regexp in (DECL_RE, DECLARE_OPERATOR_RE):
            for match in regexp.finditer(code):
                name = match.group("name")
                if name in RETIRED_COMMANDS or name in SEMANTIC_COMMANDS:
                    findings.append(Finding(
                        rel, line_number(code, match.start()), "local-definition",
                        f"local definition of \\{name}; shared notation commands are defined only in {CANONICAL_INPUT}",
                    ))

    if not canonical_source:
        for old, replacement in RETIRED_COMMANDS.items():
            pattern = re.compile(r"\\" + re.escape(old) + r"(?![A-Za-z@])")
            for match in pattern.finditer(code):
                # A declaration already has a more specific diagnostic.
                prefix = code[max(0, match.start() - 40):match.start()]
                if re.search(r"\\(?:newcommand|renewcommand|providecommand|DeclareMathOperator)\*?\s*(?:\{\s*)?$", prefix):
                    continue
                findings.append(Finding(
                    rel, line_number(code, match.start()), "retired-command",
                    f"retired \\{old}; use \\{replacement}",
                ))

        # ``\NaturalNumbers`` already owns its defining ``_0`` subscript.
        # Any following subscript is both a likely TeX double-script failure
        # and a semantic smell (the common ``>0`` case is
        # ``\PositiveIntegers``).  This catches an argument-composition defect
        # that a command-name-only audit cannot see.
        for match in re.finditer(r"\\NaturalNumbers\s*_", code):
            findings.append(Finding(
                rel,
                line_number(code, match.start()),
                "canonical-double-script",
                (
                    r"\NaturalNumbers already includes the subscript 0; "
                    r"use \PositiveIntegers or spell the intended set explicitly"
                ),
            ))

    # Literal operator spellings bypass the shared semantic command.
    literal_patterns = {
        r"\\operatorname\s*\{\s*up\s*\}": r"literal up operator; use \RvachevUp",
        r"\\mathrm\s*\{\s*up\s*\}": r"literal up operator; use \RvachevUp",
        r"\\mathop\s*\{\s*\\rm\s+up\s*\}": r"literal up operator; use \RvachevUp",
        r"\\mathcal\s*(?:\{\s*F\s*\}|F(?![A-Za-z@]))": (
            r"ambiguous calligraphic F; use \FabiusGlobal or a descriptive local symbol"
        ),
        r"\\widetilde\s*(?:\{\s*F\s*\}|F(?![A-Za-z@]))": (
            r"ambiguous tilde F; use \FabiusGlobal or a descriptive local symbol"
        ),
    }
    if not canonical_source:
        for pattern, message in literal_patterns.items():
            for match in re.finditer(pattern, code):
                findings.append(Finding(
                    rel, line_number(code, match.start()), "literal-core-symbol", message,
                ))

    literal_semantic_patterns = {
        r"\\operatorname\s*\{\s*span\s*\}": r"use \SpanOperator",
        r"\\operatorname\s*\{\s*diag\s*\}": r"use \DiagonalOperator",
        r"\\operatorname\s*\{\s*tr\s*\}": r"use \TraceOperator",
        r"\\operatorname\s*\{\s*rank\s*\}": r"use \RankOperator",
        r"\\operatorname\s*\{\s*TV\s*\}": (
            r"use \TotalVariationOf or \TotalVariationDistance"
        ),
        r"\\operatorname\s*\{\s*ord\s*\}": r"use \OrderOperator",
        r"\\operatorname\s*\{\s*wt\s*\}\s*_\s*(?:\{\s*2\s*\}|2)": (
            r"use \BinaryDigitSum"
        ),
        r"\\operatorname\s*\{\s*supp\s*\}": r"use \SupportOperator",
        r"\\operatorname\s*\{\s*sgn\s*\}": r"use \Sign",
        r"\\operatorname\s*\{\s*lcm\s*\}": r"use \LeastCommonMultiple",
        r"\\operatorname\s*\{\s*dist\s*\}": r"use \MetricDistance",
    }
    if not canonical_source:
        for pattern, message in literal_semantic_patterns.items():
            for match in re.finditer(pattern, code):
                findings.append(Finding(
                    rel,
                    line_number(code, match.start()),
                    "literal-shared-operator",
                    f"literal shared operator; {message}",
                ))

    digest = hashlib.sha256(raw.encode("utf-8-sig")).hexdigest()
    info = {
        "path": rel,
        "sha256": digest,
        "bytes": len(raw.encode("utf-8")),
        "lines": raw.count("\n") + (0 if raw.endswith("\n") else 1),
        "standalone": root,
        "canonicalInputCount": canonical_mentions,
        "inputTargets": input_targets(code),
    }
    return info, findings, commands


def print_human(report: dict, *, verbose: bool) -> None:
    inventory = report["inventory"]
    print(f"active TeX files             : {inventory['files']}")
    print(f"standalone documents         : {inventory['standalone']}")
    print(f"included/generated fragments : {inventory['fragments']}")
    print(f"source lines                 : {inventory['lines']}")
    print(f"source bytes                 : {inventory['bytes']}")
    print(f"findings                     : {inventory['findings']}")
    print()
    by_code = report["findingsByCode"]
    for code, count in sorted(by_code.items(), key=lambda item: (-item[1], item[0])):
        print(f"  {count:6d}  {code}")
    if verbose and report["findings"]:
        print()
        for item in report["findings"]:
            print(f"{item['path']}:{item['line']}: {item['message']}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", help="focused files/directories below docs")
    parser.add_argument("--strict", action="store_true", help="exit 1 when any finding exists")
    parser.add_argument("--list", action="store_true", help="print every finding")
    parser.add_argument("--json", metavar="PATH", help="write the full report as JSON")
    args = parser.parse_args()

    _fabius, docs, archive = repository_paths()
    try:
        files = active_tex_files(args.paths, docs, archive)
    except (FileNotFoundError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 2

    file_info: list[dict] = []
    findings: list[Finding] = []
    commands: Counter[str] = Counter()
    for path in files:
        info, file_findings, file_commands = audit_file(path, docs)
        file_info.append(info)
        findings.extend(file_findings)
        commands.update(file_commands)

    finding_dicts = [asdict(item) for item in findings]
    finding_counts = Counter(item.code for item in findings)
    roots = sum(bool(item["standalone"]) for item in file_info)
    report = {
        "schemaVersion": 1,
        "notationVersion": "2026-08-31",
        "scope": "Analysis/FabiusFunction/docs/**/*.tex excluding docs/archive/**",
        "inventory": {
            "files": len(file_info),
            "standalone": roots,
            "fragments": len(file_info) - roots,
            "lines": sum(int(item["lines"]) for item in file_info),
            "bytes": sum(int(item["bytes"]) for item in file_info),
            "findings": len(findings),
        },
        "findingsByCode": dict(sorted(finding_counts.items())),
        "commands": dict(sorted(commands.items())),
        "files": file_info,
        "findings": finding_dicts,
    }

    print_human(report, verbose=args.list)
    if args.json:
        output = Path(args.json)
        output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"\nwrote {output}")
    return 1 if args.strict and findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
