#!/usr/bin/env python3
"""Apply the mechanically safe part of the Fabius TeX notation migration.

This helper performs only transformations whose old command has one semantic
meaning and the same TeX argument shape as its canonical replacement.  It:

* adds the relative ``fabius-notation.tex`` input to standalone documents;
* removes one-line local definitions of commands it can rename safely; and
* renames command tokens without touching comments or ``docs/archive``.

Normalization-sensitive work is intentionally excluded: sinc, Fourier,
Fabius/global ``F`` symbols, Thue--Morse sign aliases, q-series commands, and
multi-line macro definitions require semantic review.  Run the strict audit
after this helper and finish those findings by hand.

The command is dry-run by default and accepts one or more explicit files or
directories.  ``--apply`` is required to write.  Archive paths are rejected.

Examples::

    python Analysis/FabiusFunction/scripts/migrate_tex_notation.py Analysis/FabiusFunction/docs/foo
    python Analysis/FabiusFunction/scripts/migrate_tex_notation.py --apply Analysis/FabiusFunction/docs/foo
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys


CANONICAL_INPUT = "fabius-notation.tex"

# Every entry here preserves TeX argument shape after the explicit positive-
# integer special case in ``transform`` has run.  Do not add normalization-
# sensitive or variadic commands merely to reduce the audit count.
SAFE_RENAMES = {
    "R": "RealNumbers",
    "C": "ComplexNumbers",
    "Q": "RationalNumbers",
    "N": "NaturalNumbers",
    "Z": "IntegerNumbers",
    "Up": "RvachevUp",
    "up": "RvachevUp",
    "upf": "RvachevUp",
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
    "bigO": "BigO",
    "Oh": "BigO",
    "smallo": "LittleO",
    "littleo": "LittleO",
    "littleoh": "LittleO",
    "supp": "SupportOperator",
    "sgn": "Sign",
    "lcm": "LeastCommonMultiple",
    "ord": "OrderOperator",
    "vtwo": "TwoAdicValuation",
    "Law": "LawOperator",
    "Lop": "LaplaceTransformSymbol",
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
    "InvF": "FabiusClampedQuantile",
}

# Literal operator spellings duplicate a canonical command even when no local
# alias is involved.  These replacements preserve the following argument
# syntax exactly; the binary-weight pattern additionally consumes its fixed
# base-2 subscript because ``\BinaryDigitSum`` already owns that decoration.
SAFE_LITERAL_RENAMES = (
    ("operator-span", r"\\operatorname\s*\{\s*span\s*\}", "SpanOperator"),
    ("operator-diag", r"\\operatorname\s*\{\s*diag\s*\}", "DiagonalOperator"),
    ("operator-tr", r"\\operatorname\s*\{\s*tr\s*\}", "TraceOperator"),
    ("operator-rank", r"\\operatorname\s*\{\s*rank\s*\}", "RankOperator"),
    ("operator-ord", r"\\operatorname\s*\{\s*ord\s*\}", "OrderOperator"),
    (
        "operator-binary-weight",
        r"\\operatorname\s*\{\s*wt\s*\}\s*_\s*(?:\{\s*2\s*\}|2)",
        "BinaryDigitSum",
    ),
    ("operator-supp", r"\\operatorname\s*\{\s*supp\s*\}", "SupportOperator"),
    ("operator-sgn", r"\\operatorname\s*\{\s*sgn\s*\}", "Sign"),
    ("operator-lcm", r"\\operatorname\s*\{\s*lcm\s*\}", "LeastCommonMultiple"),
    ("operator-dist", r"\\operatorname\s*\{\s*dist\s*\}", "MetricDistance"),
)

DOCUMENTCLASS_RE = re.compile(r"(?m)^[^%\n]*\\documentclass(?:\[[^]]*\])?\{")
CANONICAL_INPUT_RE = re.compile(
    r"\\input\s*\{[^}\n]*" + re.escape(CANONICAL_INPUT) + r"\s*\}"
)
DECL_PATTERNS = {
    name: re.compile(
        r"^[ \t]*\\(?:newcommand|renewcommand|providecommand)\*?\s*"
        r"(?:\{\s*)?\\" + re.escape(name) + r"(?![A-Za-z@])"
        r"|^[ \t]*\\DeclareMathOperator\*?\s*(?:\{\s*)?\\"
        + re.escape(name) + r"(?![A-Za-z@])"
        r"|^[ \t]*\\def\s*\\" + re.escape(name) + r"(?![A-Za-z@])"
    )
    for name in SAFE_RENAMES
}


def repository_paths() -> tuple[Path, Path]:
    fabius = Path(__file__).resolve().parent.parent
    return fabius / "docs", fabius / "docs" / "archive"


def is_under(path: Path, parent: Path) -> bool:
    try:
        path.resolve().relative_to(parent.resolve())
        return True
    except ValueError:
        return False


def collect(arguments: list[str], docs: Path, archive: Path) -> list[Path]:
    if not arguments:
        raise ValueError("at least one explicit file or directory is required")
    found: set[Path] = set()
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
                # A parent directory such as docs/ legitimately contains the
                # excluded archive subtree.  Explicit archive arguments were
                # rejected above; recursive discovery simply omits them.
                continue
            if candidate.name == CANONICAL_INPUT:
                continue
            found.add(candidate)
    return sorted(found)


def comment_offset(line: str) -> int | None:
    for index, char in enumerate(line):
        if char != "%":
            continue
        backslashes = 0
        cursor = index - 1
        while cursor >= 0 and line[cursor] == "\\":
            backslashes += 1
            cursor -= 1
        if backslashes % 2 == 0:
            return index
    return None


def split_code_comment(line: str) -> tuple[str, str]:
    offset = comment_offset(line)
    return (line, "") if offset is None else (line[:offset], line[offset:])


def declaration_name(code: str, extra_names: set[str]) -> str | None:
    patterns = dict(DECL_PATTERNS)
    for name in extra_names:
        patterns[name] = re.compile(
            r"^[ \t]*\\(?:newcommand|renewcommand|providecommand)\*?\s*"
            r"(?:\{\s*)?\\" + re.escape(name) + r"(?![A-Za-z@])"
            r"|^[ \t]*\\DeclareMathOperator\*?\s*(?:\{\s*)?\\"
            + re.escape(name) + r"(?![A-Za-z@])"
            r"|^[ \t]*\\def\s*\\" + re.escape(name) + r"(?![A-Za-z@])"
        )
    for name, regexp in patterns.items():
        if regexp.search(code):
            return name
    return None


def canonical_relative_input(path: Path, docs: Path) -> str:
    target = docs / CANONICAL_INPUT
    relative = Path(*Path(target).relative_to(path.parent).parts) if is_under(target, path.parent) else None
    if relative is None:
        import os
        value = os.path.relpath(target, path.parent)
    else:
        value = str(relative)
    return value.replace("\\", "/")


def add_input(text: str, path: Path, docs: Path) -> tuple[str, bool]:
    if not DOCUMENTCLASS_RE.search(text) or CANONICAL_INPUT_RE.search(text):
        return text, False
    lines = text.splitlines(keepends=True)
    begin = next(
        (index for index, line in enumerate(lines) if "\\begin{document}" in split_code_comment(line)[0]),
        None,
    )
    if begin is None:
        raise ValueError(f"standalone document has no \\begin{{document}}: {path}")

    insertion = None
    for index, line in enumerate(lines[:begin]):
        code, _comment = split_code_comment(line)
        if re.search(r"\\(?:newcommand|renewcommand|providecommand|DeclareMathOperator|newtheorem)\b", code):
            insertion = index
            break
    if insertion is None:
        insertion = begin
    newline = "\r\n" if "\r\n" in text else "\n"
    relative = canonical_relative_input(path, docs)
    lines.insert(
        insertion,
        f"% Canonical project-wide mathematical notation.{newline}"
        f"\\input{{{relative}}}{newline}",
    )
    return "".join(lines), True


def transform(
    text: str,
    path: Path,
    docs: Path,
    *,
    replace_global_fabius: bool,
    sinc_normalization: str | None,
    thue_morse_symbol: bool,
    gaussian_binomial_three: bool,
    ordinary_rising_poch: bool,
) -> tuple[str, dict[str, int], bool]:
    text, added = add_input(text, path, docs)
    renames = dict(SAFE_RENAMES)
    if sinc_normalization == "rad":
        renames["sinc"] = "SincRad"
    elif sinc_normalization == "pi":
        renames["sinc"] = "SincPi"
    if thue_morse_symbol:
        renames["tm"] = "ThueMorseSignSymbol"
        renames["TM"] = "ThueMorseSignSymbol"
    if gaussian_binomial_three:
        renames["qbinom"] = "GaussianBinomial"
    if ordinary_rising_poch:
        renames["poch"] = "RisingFactorial"
    extra_names = set(renames) - set(SAFE_RENAMES)
    counts = {name: 0 for name in renames}
    output: list[str] = []
    for line in text.splitlines(keepends=True):
        code, comment = split_code_comment(line)
        name = declaration_name(code, extra_names)
        if name is not None:
            # Only one-line definitions are mechanical.  A continuation marker
            # or unbalanced braces is left for semantic review.
            if not code.rstrip().endswith("%") and code.count("{") == code.count("}"):
                counts[name] += 1
                continue
        # ``\NaturalNumbers`` deliberately renders N with a built-in zero
        # subscript.  Therefore a token-only rename of ``\N_{>0}`` would
        # produce a double subscript and, worse, would misstate the intended
        # positive-integer domain.  Consume this exact legacy composite before
        # applying the generic argument-shape-preserving command renames.
        code, substitutions = re.subn(
            r"\\N\s*_\s*\{\s*>\s*0\s*\}",
            r"\\PositiveIntegers",
            code,
        )
        if substitutions:
            counts["N-positive"] = counts.get("N-positive", 0) + substitutions
        code, substitutions = re.subn(
            r"\\NaturalNumbers\s*_\s*\{\s*(?:>\s*0|\\geq?\s*1)\s*\}",
            r"\\PositiveIntegers",
            code,
        )
        if substitutions:
            counts["NaturalNumbers-positive"] = (
                counts.get("NaturalNumbers-positive", 0) + substitutions
            )
        code, substitutions = re.subn(
            r"\\NaturalNumbers\s*_\s*0(?![0-9])",
            r"\\NaturalNumbers",
            code,
        )
        if substitutions:
            counts["NaturalNumbers-redundant-zero"] = (
                counts.get("NaturalNumbers-redundant-zero", 0) + substitutions
            )
        for old, new in renames.items():
            pattern = re.compile(r"\\" + re.escape(old) + r"(?![A-Za-z@])")
            code, substitutions = pattern.subn(r"\\" + new, code)
            counts[old] += substitutions
        for key, pattern, replacement in SAFE_LITERAL_RENAMES:
            # The source pattern ends in a closing brace, whereas the target
            # is a control word.  Keep a trailing separator so a following
            # letter cannot be swallowed into the replacement command name.
            code, substitutions = re.subn(pattern, r"\\" + replacement + " ", code)
            if substitutions:
                counts[key] = counts.get(key, 0) + substitutions
        if replace_global_fabius:
            for pattern in (
                r"\\mathcal\s*\{\s*F\s*\}",
                r"\\mathcal\s+F(?![A-Za-z@])",
                r"\\widetilde\s*\{\s*F\s*\}",
                r"\\widetilde\s+F(?![A-Za-z@])",
            ):
                code, substitutions = re.subn(pattern, r"\\FabiusGlobal", code)
                if substitutions:
                    counts["FabiusGlobal-literal"] = (
                        counts.get("FabiusGlobal-literal", 0) + substitutions
                    )
        output.append(code + comment)
    return "".join(output), {k: v for k, v in counts.items() if v}, added


def read_exact(path: Path) -> tuple[str, str]:
    raw = path.read_bytes()
    encoding = "utf-8-sig" if raw.startswith(b"\xef\xbb\xbf") else "utf-8"
    return raw.decode(encoding), encoding


def write_exact(path: Path, text: str, encoding: str) -> None:
    path.write_bytes(text.encode(encoding))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", help="explicit files/directories below docs")
    parser.add_argument("--apply", action="store_true", help="write transformed files")
    parser.add_argument(
        "--replace-global-fabius",
        action="store_true",
        help="semantically assert that literal mathcal/tilde F denotes FabiusGlobal",
    )
    parser.add_argument(
        "--sinc-normalization",
        choices=("rad", "pi"),
        help="semantically assert sinc(z)=sin(z)/z or sinc_pi(x)=sin(pi*x)/(pi*x)",
    )
    parser.add_argument(
        "--thue-morse-symbol",
        action="store_true",
        help="semantically assert that legacy tm/TM macros denote the Thue-Morse sign symbol",
    )
    parser.add_argument(
        "--gaussian-binomial-three",
        action="store_true",
        help="semantically assert that qbinom already has three explicit arguments n, k, q",
    )
    parser.add_argument(
        "--ordinary-rising-poch",
        action="store_true",
        help="semantically assert that legacy two-argument poch denotes the ordinary rising factorial",
    )
    args = parser.parse_args()
    docs, archive = repository_paths()
    try:
        files = collect(args.paths, docs, archive)
    except (FileNotFoundError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 2

    changed = 0
    total = {name: 0 for name in SAFE_RENAMES}
    roots_updated = 0
    for path in files:
        original, encoding = read_exact(path)
        try:
            migrated, counts, input_added = transform(
                original,
                path,
                docs,
                replace_global_fabius=args.replace_global_fabius,
                sinc_normalization=args.sinc_normalization,
                thue_morse_symbol=args.thue_morse_symbol,
                gaussian_binomial_three=args.gaussian_binomial_three,
                ordinary_rising_poch=args.ordinary_rising_poch,
            )
        except ValueError as error:
            print(str(error), file=sys.stderr)
            return 2
        if migrated == original:
            continue
        changed += 1
        roots_updated += int(input_added)
        for name, count in counts.items():
            total[name] = total.get(name, 0) + count
        action = "WRITE" if args.apply else "WOULD WRITE"
        print(f"{action} {path.relative_to(docs).as_posix()}")
        if args.apply:
            write_exact(path, migrated, encoding)

    print()
    print(f"files scanned       : {len(files)}")
    print(f"files changed       : {changed}")
    print(f"root imports added  : {roots_updated}")
    print("token/definition rewrites:")
    for name, count in sorted(total.items(), key=lambda item: (-item[1], item[0])):
        if not count:
            continue
        if name == "FabiusGlobal-literal":
            print(f"  {count:6d}  literal mathcal/tilde F -> \\FabiusGlobal")
        elif name == "N-positive":
            print(f"  {count:6d}  \\N_{{>0}} -> \\PositiveIntegers")
        elif name == "NaturalNumbers-positive":
            print(f"  {count:6d}  scripted \\NaturalNumbers -> \\PositiveIntegers")
        elif name == "NaturalNumbers-redundant-zero":
            print(f"  {count:6d}  \\NaturalNumbers_0 -> \\NaturalNumbers")
        elif name.startswith("operator-"):
            target = next(
                replacement
                for key, _pattern, replacement in SAFE_LITERAL_RENAMES
                if key == name
            )
            print(f"  {count:6d}  literal {name[9:]} operator -> \\{target}")
        elif name in SAFE_RENAMES:
            print(f"  {count:6d}  \\{name} -> \\{SAFE_RENAMES[name]}")
        elif name == "sinc":
            target = "SincRad" if args.sinc_normalization == "rad" else "SincPi"
            print(f"  {count:6d}  \\sinc -> \\{target}")
        elif name in {"tm", "TM"}:
            print(f"  {count:6d}  \\{name} -> \\ThueMorseSignSymbol")
        elif name == "qbinom":
            print(f"  {count:6d}  \\qbinom -> \\GaussianBinomial")
        else:
            print(f"  {count:6d}  \\poch -> \\RisingFactorial")
    if not args.apply and changed:
        print("\ndry run only; rerun with --apply to write")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
