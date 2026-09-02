#!/usr/bin/env python3
r"""Apply the mechanically safe part of the Fabius TeX notation migration.

This helper performs only transformations whose old command has one semantic
meaning and the same TeX argument shape as its canonical replacement.  It:

* adds the relative ``fabius-notation.tex`` input to standalone documents;
* removes one-line local definitions of commands it can rename safely; and
* renames command tokens without touching comments or ``docs/archive``.

Normalization-sensitive work is intentionally excluded: sinc, Fourier,
Fabius/global ``F`` symbols, Thue--Morse sign aliases, q-series commands, and
multi-line macro definitions require semantic review.  Run the strict audit
after this helper and finish those findings by hand.

The opt-in ``--combinatorial-calculus`` profile applies the reviewed,
argument-shape-preserving renames shared by the six combinatorial coefficient
calculus reports.  It also removes their superseded one-line local definitions
and the corresponding non-Fourier-hat markers.

The opt-in ``--formal-bigo-filtration`` profile rewrites a reviewed formal-tail
spelling such as ``\FormalBigO_t(E)`` to the explicit two-argument command
``\FormalBigOAt{E}{t}``.  Its balanced-parenthesis parser preserves nested
operands and rejects any occurrence whose wrapper is not understood.

The opt-in ``--classical-analysis-aliases`` profile retires the reviewed
``\falling``, ``\rising``, ``\pos``, and mixed-grammar ``\Mellin`` aliases.
The Mellin migration recognizes only the application and bare-operator forms
present in the audited corpus and fails closed if another form is encountered.

The opt-in ``--two-adic-valuation`` profile retires the reviewed local aliases
for the specialized two-adic valuation and rewrites a classified literal
``\nu_2`` to ``\TwoAdicValuation``.  It skips whole-paper historical notation
scopes and fails closed if an unclassified literal remains in a selected
project-authored source.

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
HISTORICAL_NOTATION_MARKER = "HISTORICAL-NOTATION-SCOPE"

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
    "OO": "BigO",
    "bigOPartl": "BigO",
    "smallo": "LittleO",
    "smalloPartl": "LittleO",
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

# These names are safe only after the caller has asserted that the selected
# sources are the reviewed combinatorial-coefficient-calculus reports.  Keeping
# them behind an explicit profile prevents a generic local ``Bell`` or
# ``PosetMinimum`` command elsewhere in the corpus from being reclassified.
COMBINATORIAL_CALCULUS_RENAMES = {
    "stirone": "UnsignedStirlingFirstKind",
    "stirtwo": "StirlingSecondKind",
    "eulerian": "TypeAEulerianNumber",
    "eulertwo": "SecondOrderEulerianNumber",
    "Bell": "BellNumber",
    "BellP": "ExponentialPartialBellPolynomial",
    "BellC": "ExponentialCompleteBellPolynomial",
    "OrdinaryBellPolynomial": "OrdinaryPartialBellPolynomial",
    "OrdinaryBellSeriesOf": "OrdinaryGeneratingFunctionOf",
    "OrdinaryGeneratingSeriesOf": "OrdinaryGeneratingFunctionOf",
    "NormalizedInverseCoefficient": "NormalizedReversionCoefficient",
    "PosetMinimum": "PartitionLatticeMinimum",
    "PosetMaximum": "PartitionLatticeMaximum",
    "TracePowerSum": "TraceBellArgument",
    "coeff": "CoefficientExtraction",
    "cyc": "CycleCountOperator",
    "setpart": "SetPartitionOperator",
    "bitand": "BitwiseAnd",
}

COMBINATORIAL_SHARED_DECLARATIONS = {
    "FiniteField",
    "OrdinaryPartialBellPolynomial",
    "ExponentialGeneratingFunctionOf",
    "NormalizedReversionCoefficient",
    "NormalizedOrdinaryCoefficient",
    "PartitionLatticeMinimum",
    "PartitionLatticeMaximum",
    "TraceBellArgument",
}

COMBINATORIAL_PROMOTED_LOCAL_ACCENTS = {
    "OrdinaryPartialBellPolynomial",
    "ExponentialGeneratingFunctionOf",
    "OrdinaryBellSeriesOf",
    "NormalizedInverseCoefficient",
    "PartitionLatticeMinimum",
    "PartitionLatticeMaximum",
}

CLASSICAL_ANALYSIS_RENAMES = {
    "falling": "FallingFactorial",
    "rising": "RisingFactorial",
    "pos": "PositivePart",
}

CLASSICAL_ANALYSIS_SHARED_DECLARATIONS = {"Mellin"}

TWO_ADIC_VALUATION_RENAMES = {
    "nuu": "TwoAdicValuation",
    "nuTwo": "TwoAdicValuation",
    "vTwo": "TwoAdicValuation",
    "vtwoPartii": "TwoAdicValuation",
    "vtwoPartcc": "TwoAdicValuation",
}

TWO_ADIC_VALUATION_DEFINITION_BODIES = {
    "nuu": r"\nu_2",
    "nuTwo": r"\nu_2",
    "vTwo": r"\nu_2",
    "vtwoPartii": r"\TwoAdicValuation",
    "vtwoPartcc": r"\TwoAdicValuation",
}

# The final boundary deliberately rejects a following letter or digit.  A
# source such as ``\nu_{2a}``, ``\nu_20``, or even juxtaposed ``\nu_{2}n``
# needs human classification rather than a replacement that could join the
# following letter to the canonical control word.
RAW_TWO_ADIC_LITERAL_RE = re.compile(
    r"(?:\\nu(?![A-Za-z@])|\{\s*\\nu(?![A-Za-z@])\s*\})"
    r"\s*_\s*"
    r"(?:"
    r"2(?![0-9A-Za-z])"
    r"|"
    r"\{\s*(?:\\[!,;:]\s*)*"
    r"(?:\\(?:displaystyle|textstyle|scriptstyle|scriptscriptstyle)\s*)?"
    r"2\s*\}(?![A-Za-z@])"
    r")"
)

# The postcondition is intentionally broader than the replacement grammar.
# It catches ambiguous TeX such as ``\nu_2n`` or ``\nu_{2}n``: those forms
# must not be rewritten automatically, but neither may they silently pass as
# if no raw valuation token remained.
ANY_RAW_TWO_ADIC_LITERAL_RE = re.compile(
    r"(?:\\nu(?![A-Za-z@])|\{\s*\\nu(?![A-Za-z@])\s*\})"
    r"\s*_\s*"
    r"(?:"
    r"2"
    r"|"
    r"\{\s*(?:\\[!,;:]\s*)*"
    r"(?:\\(?:displaystyle|textstyle|scriptstyle|scriptscriptstyle)\s*)?"
    r"2\s*\}"
    r")"
)

# These are complete for the reviewed active corpus.  They deliberately use
# literal spellings rather than a permissive operand regex: bracketed Mellin
# operands may themselves contain brackets, and inventing a partial TeX parser
# here would be less safe than rejecting any future grammar for human review.
CLASSICAL_MELLIN_REPLACEMENTS = (
    (r"\Mellin[\log L_a](w)", r"\MellinTransformOf{\log L_a}(w)"),
    (r"\Mellin\mathcal E(w)", r"\MellinTransformOf{\mathcal E}(w)"),
    (r"\xrightarrow{\ \Mellin\ }", r"\xrightarrow{\ \MellinTransformSymbol\ }"),
    (r"\Mellin_F", r"\MellinTransformOf{F}"),
    (r"\Mellin_G", r"\MellinTransformOf{G}"),
    (
        r"\Mellin[\RvachevUp|_{[0,1]}]",
        r"\MellinTransformOf{\RvachevUp|_{[0,1]}}",
    ),
    (r"\Mellin[F']", r"\MellinTransformOf{F'}"),
    (r"\Mellin[F]", r"\MellinTransformOf{F}"),
    (r"(\Mellin f)(z)", r"\MellinTransformOf{f}(z)"),
    (r"\Mellin[f(q^kx)](z)", r"\MellinTransformOf{f(q^kx)}(z)"),
    (r"\Mellin[\Gop_{n,q}f](z)", r"\MellinTransformOf{\Gop_{n,q}f}(z)"),
)

LOCAL_ACCENT_MARKER_RE = re.compile(
    r"^[ \t]*%[ \t]*LOCAL-NON-FOURIER-HAT:[ \t]*\\([A-Za-z@]+)\b"
)

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


def rewrite_formal_bigo_at(code: str, filtration: str) -> tuple[str, int]:
    r"""Make one reviewed formal filtration variable explicit.

    TeX tokenizes ``\FormalBigO_t`` as the shared zero-argument command
    ``\FormalBigO`` followed by a subscript.  The canonical replacement owns
    both the omitted expression and filtration variable.  Scan balanced round
    parentheses instead of using a regular expression so operands containing
    calls such as ``\min(...)`` remain intact.
    """

    token = rf"\FormalBigO_{filtration}"
    output: list[str] = []
    cursor = 0
    substitutions = 0
    while True:
        start = code.find(token, cursor)
        if start < 0:
            output.append(code[cursor:])
            break

        after = start + len(token)
        if after < len(code) and (code[after].isalpha() or code[after] == "@"):
            output.append(code[cursor:after])
            cursor = after
            continue

        wrapper = after
        while wrapper < len(code) and code[wrapper] in " \t":
            wrapper += 1

        scalable = re.match(r"\\!\s*\\left\s*\(", code[wrapper:])
        if scalable is not None:
            opening = wrapper + scalable.end() - 1
        elif wrapper < len(code) and code[wrapper] == "(":
            opening = wrapper
        else:
            raise ValueError(
                f"unsupported formal-tail wrapper after {token}: "
                f"{code[start:start + 80]!r}"
            )

        depth = 0
        closing: int | None = None
        for index in range(opening, len(code)):
            if code[index] == "(":
                depth += 1
            elif code[index] == ")":
                depth -= 1
                if depth == 0:
                    closing = index
                    break
        if closing is None:
            raise ValueError(f"unbalanced formal-tail operand after {token}")

        operand = code[opening + 1 : closing]
        if scalable is not None:
            right = re.search(r"\\right\s*$", operand)
            if right is None:
                raise ValueError(f"scalable formal-tail wrapper lacks \\right after {token}")
            operand = operand[: right.start()]

        output.append(code[cursor:start])
        output.append(rf"\FormalBigOAt{{{operand}}}{{{filtration}}}")
        cursor = closing + 1
        substitutions += 1

    return "".join(output), substitutions


def rewrite_classical_analysis_aliases(code: str) -> tuple[str, dict[str, int]]:
    r"""Rewrite the reviewed nonuniform falling-factorial and Mellin forms."""

    counts: dict[str, int] = {}
    code, substitutions = re.subn(
        r"\\falling\s+D\s*n(?![A-Za-z@])",
        r"\\FallingFactorial{D}{n}",
        code,
    )
    if substitutions:
        counts["falling-implicit-Dn"] = substitutions

    mellin_substitutions = 0
    for old, new in CLASSICAL_MELLIN_REPLACEMENTS:
        occurrences = code.count(old)
        if occurrences:
            code = code.replace(old, new)
            mellin_substitutions += occurrences
    if mellin_substitutions:
        counts["Mellin-application"] = mellin_substitutions

    leftover = re.search(r"\\Mellin(?![A-Za-z@])", code)
    if leftover is not None:
        excerpt = code[leftover.start() : leftover.start() + 100]
        raise ValueError(f"unsupported classical Mellin alias form: {excerpt!r}")

    return code, counts


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


def is_reviewed_two_adic_definition(code: str, name: str) -> bool:
    """Accept only the five audited, zero-argument alias definitions."""

    body = TWO_ADIC_VALUATION_DEFINITION_BODIES[name]
    return bool(
        re.fullmatch(
            r"[ \t]*\\newcommand[ \t]*\{[ \t]*\\"
            + re.escape(name)
            + r"[ \t]*\}[ \t]*\{[ \t]*"
            + re.escape(body)
            + r"[ \t]*\}[ \t]*(?:\r?\n)?",
            code,
        )
    )


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
    combinatorial_calculus: bool,
    formal_bigo_filtration: str | None,
    classical_analysis_aliases: bool = False,
    two_adic_valuation: bool = False,
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
    if combinatorial_calculus:
        renames.update(COMBINATORIAL_CALCULUS_RENAMES)
    if classical_analysis_aliases:
        renames.update(CLASSICAL_ANALYSIS_RENAMES)
    if two_adic_valuation:
        renames.update(TWO_ADIC_VALUATION_RENAMES)
    shared_declarations: set[str] = set()
    if combinatorial_calculus:
        shared_declarations.update(COMBINATORIAL_SHARED_DECLARATIONS)
    if classical_analysis_aliases:
        shared_declarations.update(CLASSICAL_ANALYSIS_SHARED_DECLARATIONS)
    extra_names = (set(renames) - set(SAFE_RENAMES)) | shared_declarations
    counts = {name: 0 for name in renames}
    output: list[str] = []
    for line in text.splitlines(keepends=True):
        if combinatorial_calculus:
            marker = LOCAL_ACCENT_MARKER_RE.match(line)
            if marker and marker.group(1) in COMBINATORIAL_PROMOTED_LOCAL_ACCENTS:
                key = f"local-accent-marker-{marker.group(1)}"
                counts[key] = counts.get(key, 0) + 1
                continue
        code, comment = split_code_comment(line)
        name = declaration_name(code, extra_names)
        if name is not None:
            if two_adic_valuation and name in TWO_ADIC_VALUATION_RENAMES:
                if not is_reviewed_two_adic_definition(code, name):
                    raise ValueError(
                        f"{path}: refusing unreviewed definition of \\{name}; "
                        "the two-adic profile removes only its audited "
                        "zero-argument alias definition"
                    )
            # Only one-line definitions are mechanical.  A continuation marker
            # or unbalanced braces is left for semantic review.
            if not code.rstrip().endswith("%") and code.count("{") == code.count("}"):
                key = (
                    f"shared-definition-{name}"
                    if name in shared_declarations and name not in renames
                    else name
                )
                counts[key] = counts.get(key, 0) + 1
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
        if combinatorial_calculus:
            code, substitutions = re.subn(
                r"\\NormalizedReversionCoefficient\s*\{([^{}\r\n]+)\}"
                r"(?!\s*\{)",
                r"\\NormalizedReversionCoefficient{f}{\1}",
                code,
            )
            if substitutions:
                counts["normalized-reversion-implicit-f"] = (
                    counts.get("normalized-reversion-implicit-f", 0) + substitutions
                )
            code, substitutions = re.subn(
                r"\\NormalizedOrdinaryCoefficient\s*\{([^{}\r\n]+)\}",
                r"\\OrdinaryGeneratingCoefficient{x}{\1}",
                code,
            )
            if substitutions:
                counts["ordinary-coefficient-implicit-x"] = (
                    counts.get("ordinary-coefficient-implicit-x", 0) + substitutions
                )
        if formal_bigo_filtration is not None:
            code, substitutions = rewrite_formal_bigo_at(code, formal_bigo_filtration)
            if substitutions:
                key = f"formal-bigo-{formal_bigo_filtration}"
                counts[key] = counts.get(key, 0) + substitutions
        if classical_analysis_aliases:
            code, profile_counts = rewrite_classical_analysis_aliases(code)
            for key, substitutions in profile_counts.items():
                counts[key] = counts.get(key, 0) + substitutions
        if two_adic_valuation:
            code, substitutions = RAW_TWO_ADIC_LITERAL_RE.subn(
                r"\\TwoAdicValuation", code
            )
            if substitutions:
                counts["two-adic-literal"] = (
                    counts.get("two-adic-literal", 0) + substitutions
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
    migrated = "".join(output)
    if two_adic_valuation:
        for line_number, line in enumerate(migrated.splitlines(), start=1):
            code, _comment = split_code_comment(line)
            if ANY_RAW_TWO_ADIC_LITERAL_RE.search(code):
                raise ValueError(
                    f"{path}: unclassified raw \\nu_2 remains at line "
                    f"{line_number}; rename a non-valuation local family "
                    r"semantically or use \TwoAdicValuation"
                )
    return migrated, {k: v for k, v in counts.items() if v}, added


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
    parser.add_argument(
        "--combinatorial-calculus",
        action="store_true",
        help=(
            "semantically assert the reviewed shared namespace of the six "
            "combinatorial-coefficient-calculus reports"
        ),
    )
    parser.add_argument(
        "--formal-bigo-filtration",
        choices=("t", "r", "x"),
        help=(
            "semantically assert the selected formal-tail subscript and rewrite "
            "its balanced parenthesized operands to FormalBigOAt"
        ),
    )
    parser.add_argument(
        "--classical-analysis-aliases",
        action="store_true",
        help=(
            "semantically assert the reviewed falling/rising/positive-part "
            "aliases and the corpus-specific Mellin application grammar"
        ),
    )
    parser.add_argument(
        "--two-adic-valuation",
        action="store_true",
        help=(
            "semantically assert that reviewed local aliases and raw nu_2 "
            "literals denote the specialized two-adic valuation"
        ),
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
    historical_scopes_skipped = 0
    for path in files:
        original, encoding = read_exact(path)
        historical_source = (docs / "papers").resolve() in path.resolve().parents
        if (
            args.two_adic_valuation
            and historical_source
            and HISTORICAL_NOTATION_MARKER in original
        ):
            historical_scopes_skipped += 1
            print(
                "SKIP HISTORICAL NOTATION SCOPE "
                f"{path.relative_to(docs).as_posix()}"
            )
            continue
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
                combinatorial_calculus=args.combinatorial_calculus,
                formal_bigo_filtration=args.formal_bigo_filtration,
                classical_analysis_aliases=args.classical_analysis_aliases,
                two_adic_valuation=args.two_adic_valuation,
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
    print(f"historical scopes skipped: {historical_scopes_skipped}")
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
        elif name in COMBINATORIAL_CALCULUS_RENAMES:
            print(
                f"  {count:6d}  \\{name} -> "
                f"\\{COMBINATORIAL_CALCULUS_RENAMES[name]}"
            )
        elif name.startswith("shared-definition-"):
            print(f"  {count:6d}  remove local \\{name[18:]} definition")
        elif name.startswith("local-accent-marker-"):
            print(f"  {count:6d}  remove local-hat marker for \\{name[20:]}")
        elif name == "normalized-reversion-implicit-f":
            print(
                f"  {count:6d}  make the normalized reversion family f explicit"
            )
        elif name == "ordinary-coefficient-implicit-x":
            print(
                f"  {count:6d}  make the ordinary coefficient family x explicit"
            )
        elif name.startswith("formal-bigo-"):
            filtration = name.removeprefix("formal-bigo-")
            print(
                f"  {count:6d}  \\FormalBigO_{filtration}(...) -> "
                f"\\FormalBigOAt{{...}}{{{filtration}}}"
            )
        elif name == "falling-implicit-Dn":
            print(
                f"  {count:6d}  \\falling Dn -> "
                r"\FallingFactorial{D}{n}"
            )
        elif name == "Mellin-application":
            print(
                f"  {count:6d}  reviewed \\Mellin applications -> "
                r"\MellinTransformOf / \MellinTransformSymbol"
            )
        elif name == "two-adic-literal":
            print(
                f"  {count:6d}  literal \\nu_2 -> "
                r"\TwoAdicValuation"
            )
        elif name in TWO_ADIC_VALUATION_RENAMES:
            print(
                f"  {count:6d}  \\{name} -> "
                f"\\{TWO_ADIC_VALUATION_RENAMES[name]}"
            )
        elif name in CLASSICAL_ANALYSIS_RENAMES:
            print(
                f"  {count:6d}  \\{name} -> "
                f"\\{CLASSICAL_ANALYSIS_RENAMES[name]}"
            )
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
