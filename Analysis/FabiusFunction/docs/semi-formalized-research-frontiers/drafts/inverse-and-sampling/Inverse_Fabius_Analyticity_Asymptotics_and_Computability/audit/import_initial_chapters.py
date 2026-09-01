#!/usr/bin/env python3
"""Bootstrap editable canonical chapters from the immutable source snapshot.

This is intentionally a one-time editorial import, not a canonical-source
generator.  It selects the mathematically substantive ranges, prefixes TeX
identifiers, and leaves the resulting chapter files available for ordinary
human editing.  A reviewed theorem concordance, once produced, rather than
byte identity with these initial fragments, will record the final semantic
disposition of every source result.
"""

from __future__ import annotations

import re
import subprocess
from collections import OrderedDict
from pathlib import Path


PACKAGE = Path(__file__).resolve().parents[1]
AUDIT = PACKAGE / "audit"
CHAPTERS = PACKAGE / "chapters"
PIN = (AUDIT / "SOURCE_REVISION").read_text(encoding="utf-8").strip()
SOURCE_ROOT = (
    "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
    "drafts/inverse-and-sampling"
)

SOURCES = {
    "ne": (
        "Non-elementarity",
        "analyticity-and-elementarity/Non_Elementarity_of_the_Fabius_Function/"
        "Non_Elementarity_of_the_Fabius_Function.tex",
    ),
    "ii": (
        "Inverse iterates",
        "analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/"
        "inverse_fabius_iterates_nowhere_analytic.tex",
    ),
    "is": (
        "Inverse and sampling frontiers",
        "inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers/"
        "Inverse_and_Sampling_Frontiers.tex",
    ),
    "ao": (
        "All-orders endpoint asymptotics",
        "inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders/"
        "Inverse_Endpoint_All_Orders.tex",
    ),
    "co": (
        "Inverse computability",
        "inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/"
        "inverse_fabius_computability.tex",
    ),
}

CHAPTER_SPECS = OrderedDict(
    [
        (
            "00_scope_and_platform.tex",
            (
                r"\part{Scope, Status, and the Common Fabius--Rvachev Platform}"
                "\n\n"
                r"\section{The shared analytic and probabilistic platform}"
                "\n"
                r"\label{sec:common-platform}"
                "\n\n"
                "The five source reports use the same bounded Fabius function, "
                "Rvachev density, random series, Fourier product, and dyadic "
                "spline approximants.  They are fixed once in this part; later "
                "parts introduce only the notation peculiar to their question."
                "\n\n",
                [
                    (
                        "is",
                        r"\section{Established platform and notation}",
                        r"\section{Bell-polynomial transfer from forward splines to quantiles}",
                    ),
                    (
                        "ii",
                        r"\section{Fabius, Rvachev, Thue--Morse, and the derivative atlas}",
                        r"\section{Why a direct dyadic-jet induction fails}",
                    ),
                ],
            ),
        ),
        (
            "01_analyticity_and_elementarity.tex",
            (
                r"\part{Analyticity, Algebraic Branches, and Non-Elementarity}"
                "\n\n",
                [
                    (
                        "ne",
                        r"\section{Statement}",
                        r"\section{The formal development}",
                    )
                ],
            ),
        ),
        (
            "02_inverse_iterates.tex",
            (
                r"\part{Inverse Iterates and Their Taylor Obstructions}" "\n\n",
                [
                    (
                        "ii",
                        r"\section{Statement of the problem and strengthened results}",
                        r"\section{Repository audit and novelty boundary}",
                    ),
                    (
                        "ii",
                        r"\section{Why a direct dyadic-jet induction fails}",
                        r"\section{Numerical diagnostics}",
                    ),
                    (
                        "ii",
                        r"\section{Conjectures and research directions}",
                        r"\section{Reproducibility guide}",
                    ),
                ],
            ),
        ),
        (
            "03_inverse_germs_and_deconvolution.tex",
            (
                r"\part{Inverse-Dyadic Germs and Rvachev--Appell Deconvolution}"
                "\n\n",
                [
                    (
                        "is",
                        r"\section{Bell-polynomial transfer from forward splines to quantiles}",
                        r"\section{Periodic Lambert--Bell inversion at the endpoint}",
                    ),
                    (
                        "is",
                        r"\subsection{The two random series}",
                        r"\section{Algebraic Taylor shadows of the inverse Fabius function}",
                    ),
                    (
                        "is",
                        r"\subsection{Lagrange--B\"urmann and Bell formulas}",
                        r"\subsection{The midpoint: a linear Taylor shadow}",
                    ),
                    (
                        "is",
                        r"\section{Kabaya--Iri polynomials and the Rvachev Appell inverse}",
                        r"\section{Synthesis, computational consequences, and formalization roadmap}",
                    ),
                ],
            ),
        ),
        (
            "04_endpoint_all_orders.tex",
            (
                r"\part{All-Orders Endpoint Asymptotics}" "\n\n",
                [
                    (
                        "ao",
                        r"\section{Imported inputs and the two-scale inverse problem}",
                        r"\section{Verification}",
                    ),
                    (
                        "ao",
                        r"\section{Verification}",
                        r"\section{Connections across the corpus}",
                    ),
                    (
                        "ao",
                        r"\section{Proof details}",
                        r"\section{Coefficient dictionary}",
                    ),
                    (
                        "ao",
                        r"\section{Conjectures and frontier directions}",
                        r"\section{Proof details}",
                    ),
                ],
            ),
        ),
        (
            "05_dyadic_self_sampling.tex",
            (
                r"\part{Dyadic Self-Sampling and Alias Superconvergence}" "\n\n",
                [
                    (
                        "is",
                        r"\section{Normalization and established structure}",
                        r"\section{Exact and high-precision experiments}",
                    ),
                    (
                        "is",
                        r"\section{Conjectures and frontier research program}",
                        r"\section{Lean formalization roadmap}",
                    ),
                    (
                        "is",
                        r"\section{First inverse-moment Appell polynomials}",
                        r"\section{Reproducibility manifest}",
                    ),
                ],
            ),
        ),
        (
            "06_computability.tex",
            (
                r"\part{Exact Inverse Moduli and Computability}" "\n\n",
                [
                    (
                        "co",
                        r"\section{Main result and proof architecture}",
                        r"\section{Corpus audit, conventions, and nonduplication boundary}",
                    ),
                    (
                        "co",
                        r"\section{Computable-analysis definitions}",
                        r"\section{Numerical and exact-rational checks}",
                    ),
                    (
                        "co",
                        r"\section{Further deductions, conjectures, and research directions}",
                        r"\section{Conclusion}",
                    ),
                ],
            ),
        ),
    ]
)

REF_COMMAND_RE = re.compile(
    r"\\(?P<command>[cC]ref|ref|eqref|autoref|pageref)\{(?P<keys>[^}]+)\}"
)
CITE_COMMAND_RE = re.compile(
    r"\\(?P<command>cite|citep|citet|nocite)"
    r"(?P<options>(?:\[[^\]]*\])*)\{(?P<keys>[^}]+)\}"
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
BIBLIOGRAPHY_RE = re.compile(
    r"\\begin\{thebibliography\}\{[^}]*\}(.*?)"
    r"\\end\{thebibliography\}",
    re.DOTALL,
)
BIBITEM_RE = re.compile(
    r"\\bibitem(?:\[[^\]]*\])?\{(?P<key>[^}]+)\}(?P<body>.*?)"
    r"(?=(?:\\bibitem(?:\[[^\]]*\])?\{)|\Z)",
    re.DOTALL,
)


def git_blob(relative: str) -> str:
    repository = subprocess.run(
        ["git", "-C", str(PACKAGE), "rev-parse", "--show-toplevel"],
        check=True,
        stdout=subprocess.PIPE,
    ).stdout.decode("utf-8").strip()
    path = f"{SOURCE_ROOT}/{relative}"
    return subprocess.run(
        ["git", "-C", repository, "show", f"{PIN}:{path}"],
        check=True,
        stdout=subprocess.PIPE,
    ).stdout.decode("utf-8").replace("\r\n", "\n")


def slice_between(text: str, start: str, end: str, source: str) -> str:
    first = text.find(start)
    if first < 0:
        raise ValueError(f"{source}: missing start marker {start!r}")
    last = text.find(end, first + len(start))
    if last < 0:
        raise ValueError(f"{source}: missing end marker {end!r}")
    return text[first:last].rstrip() + "\n"


def prefix_keys(keys: str, prefix: str) -> str:
    return ",".join(
        f"{prefix}:{key.strip()}" for key in keys.split(",") if key.strip()
    )


def prefix_identifiers(text: str, prefix: str) -> str:
    text = LABEL_RE.sub(lambda match: rf"\label{{{prefix}:{match.group(1)}}}", text)
    text = REF_COMMAND_RE.sub(
        lambda match: (
            rf"\{match.group('command')}"
            rf"{{{prefix_keys(match.group('keys'), prefix)}}}"
        ),
        text,
    )
    text = CITE_COMMAND_RE.sub(
        lambda match: (
            rf"\{match.group('command')}{match.group('options')}"
            rf"{{{prefix_keys(match.group('keys'), prefix)}}}"
        ),
        text,
    )
    return text


def adapt_fragment(text: str, prefix: str) -> str:
    text = prefix_identifiers(text, prefix)
    if prefix == "ii":
        text = text.replace(
            "{figures/",
            "{../analyticity-and-elementarity/"
            "inverse_fabius_iterates_nowhere_analytic/figures/",
        )
    if prefix == "is":
        text = text.replace(
            "{assets/",
            "{../inverse-asymptotics-and-computability/"
            "Inverse_and_Sampling_Frontiers/assets/",
        )
    if prefix in {"ao", "co"}:
        text = text.replace(r"\begin{statusbox}", r"\begin{statuspanel}")
        text = text.replace(r"\end{statusbox}", r"\end{statuspanel}")
    return text


def write_chapters(source_texts: dict[str, str]) -> None:
    CHAPTERS.mkdir(parents=True, exist_ok=True)
    for filename, (header, fragments) in CHAPTER_SPECS.items():
        pieces = [
            "% Editorial bootstrap from the immutable source revision.\n",
            "% This file is canonical and may be edited independently.\n\n",
            header,
        ]
        for prefix, start, end in fragments:
            title, _ = SOURCES[prefix]
            raw = slice_between(source_texts[prefix], start, end, title)
            pieces.extend(
                [
                    f"\n% Source fragment: {title}; prefix {prefix}.\n",
                    adapt_fragment(raw, prefix),
                ]
            )
        (CHAPTERS / filename).write_text(
            "".join(pieces).rstrip() + "\n", encoding="utf-8", newline="\n"
        )


def write_references(source_texts: dict[str, str]) -> None:
    items: OrderedDict[str, str] = OrderedDict()
    for prefix, text in source_texts.items():
        for bibliography in BIBLIOGRAPHY_RE.findall(text):
            for match in BIBITEM_RE.finditer(bibliography):
                key = f"{prefix}:{match.group('key')}"
                body = match.group("body").strip()
                previous = items.get(key)
                if previous is None or len(body) > len(previous):
                    items[key] = body
    lines = [
        r"\clearpage",
        r"\begin{thebibliography}{99}",
        "",
    ]
    for key, body in items.items():
        lines.extend([rf"\bibitem{{{key}}}", body, ""])
    lines.extend([r"\end{thebibliography}", ""])
    (CHAPTERS / "09_references.tex").write_text(
        "\n".join(lines), encoding="utf-8", newline="\n"
    )


def main() -> None:
    source_texts = {prefix: git_blob(relative) for prefix, (_, relative) in SOURCES.items()}
    write_chapters(source_texts)
    write_references(source_texts)
    print(f"source revision: {PIN}")
    print(f"chapters written: {len(CHAPTER_SPECS) + 1}")
    for path in sorted(CHAPTERS.glob("*.tex")):
        print(f"  {path.name}: {len(path.read_text(encoding='utf-8').splitlines())} lines")


if __name__ == "__main__":
    main()
