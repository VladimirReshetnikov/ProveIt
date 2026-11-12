"""Assemble the standalone TeX source and optionally compile its PDF."""
from pathlib import Path
import argparse
import re
import subprocess

ROOT = Path(__file__).resolve().parent
NAME = "ipra_479_predecessor57"


def assemble():
    text = (ROOT / "report_body.tex").read_text()
    block = (ROOT / "mathematics/block_macros.tex").read_text()
    text = text.replace("% SUPPLEMENTARY_MATHEMATICS", block)
    checker = (ROOT / "checker/code/compact479.py").read_text()
    listing = "\\begin{lstlisting}[language=Python]\n" + checker + "\\end{lstlisting}\n"
    text = text.replace("% COMPLETE_COMPACT_SOURCE", listing)
    pieces = []
    for filename, label in [
        ("inherited_choice_basis.tex", "app:logic"),
        ("inherited_ordinary_bridge.tex", "app:ordinary"),
        ("scalar_predecessor.tex", "app:oldpred"),
        ("equality_reflection.tex", "app:eq"),
        ("primitive_recursion.tex", "app:rec"),
        ("inherited_arity_checker.tex", "app:codec"),
        ("context_first_audit.tex", "app:context"),
    ]:
        body = (ROOT / "reference" / filename).read_text()
        body = re.sub(r"(\\section\{[^\n]*\}\n)",
                      lambda m: m.group(1) + "\\label{" + label + "}\n",
                      body, count=1)
        pieces.append("\n% Attributed source: reference/" + filename + "\n" + body)
    text = text.replace("% FOUNDATIONS", "\n".join(pieces))
    (ROOT / (NAME + ".tex")).write_text(text)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true")
    args = parser.parse_args()
    assemble()
    if args.pdf:
        from pdf_build import build
        build(ROOT / (NAME + ".tex"), ROOT / (NAME + ".pdf"),
              ROOT / "evidence/pdf_build.log")


if __name__ == "__main__":
    main()
