#!/usr/bin/env python3
"""Export complete coordinate maps and TeX residual transcriptions."""
import argparse
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PROFILES = ("integer248", "integer246", "integer245")


def monomial_tex(indices):
    out = []
    for index, exponent in sorted(Counter(indices).items()):
        variable = f"x_{{{index}}}"
        out.append(variable if exponent == 1 else variable + f"^{{{exponent}}}")
    return " ".join(out)


def term_tex(coefficient, indices, first=False):
    sign = "-" if coefficient < 0 else ("" if first else "+")
    size = abs(coefficient)
    scalar = "" if size == 1 and indices else str(size)
    return sign + scalar + (" " if scalar and indices else "") + monomial_tex(indices)


def residual_tex(row, index):
    chunks, chunk = [], []
    for position, (coefficient, indices) in enumerate(row["terms"]):
        term = term_tex(coefficient, indices, first=(position == 0))
        if chunk and sum(len(x) for x in chunk) + len(term) > 92:
            chunks.append(" ".join(chunk))
            chunk = []
        chunk.append(term)
    if chunk:
        chunks.append(" ".join(chunk))
    if not chunks:
        chunks = ["0"]
    lines = [f"% Residual {index}: {row['label']}", r"\begin{align*}"]
    lines.append(f"R_{{{index}}} &= " + chunks[0] + (r" \\" if len(chunks) > 1 else ""))
    for j, chunk in enumerate(chunks[1:]):
        lines.append(r"&\quad " + chunk + (r" \\" if j < len(chunks) - 2 else ""))
    lines.append(r"\end{align*}")
    return "\n".join(lines)


def render(output):
    for profile in PROFILES:
        eq = json.loads((ROOT / "equations" / profile / "equation.json").read_text())
        target = output / profile
        target.mkdir(parents=True, exist_ok=True)
        variables = "index\tname\tkind\n" + "".join(
            f"{j}\t{v['name']}\t{v['kind']}\n" for j, v in enumerate(eq["variables"]))
        (target / "variables.tsv").write_text(variables)
        body = "\n\n".join(residual_tex(row, j) for j, row in enumerate(eq["residuals"])) + "\n"
        (target / "residuals.tex").write_text(body)
        n, count = len(eq["variables"]), len(eq["residuals"])
        document = (r"\documentclass[10pt]{article}" + "\n" +
            r"\usepackage[a4paper,margin=22mm]{geometry}" + "\n" +
            r"\usepackage{amsmath,amssymb}" + "\n" +
            r"\allowdisplaybreaks" + "\n" +
            r"\begin{document}" + "\n" +
            r"\section*{Complete residual transcription: " + profile + "}\n" +
            f"All {n} variables range over the integers. Indices begin at zero.\n" +
            r"\[P(x_0,\ldots,x_{" + str(n - 1) + r"})=\sum_{j=0}^{" + str(count - 1) + r"}R_j(x)^2.\]" + "\n" +
            "This transcription is generated from the delivered literal equation JSON.\n" +
            r"\input{residuals.tex}" + "\n" + r"\end{document}" + "\n")
        (target / "equation.tex").write_text(document)
    return len(PROFILES)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps({"profiles_rendered": render(args.output)}))
