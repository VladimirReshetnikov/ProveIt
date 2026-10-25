#!/usr/bin/env python3
"""Export the complete polynomial residuals in text, TeX, and coordinate TSV."""
import argparse
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def term(coefficient, monomial, tex=False):
    c = abs(coefficient)
    factors = []
    for v, power in sorted(Counter(monomial).items()):
        if tex:
            x = "x_{" + str(v) + "}"
            if power != 1:
                x += "^{" + str(power) + "}"
        else:
            x = "x" + str(v)
            if power != 1:
                x += "^" + str(power)
        factors.append(x)
    if factors:
        body = ("" if c == 1 else str(c)) + ("" if tex else "*").join(factors)
        if not tex and c != 1:
            body = str(c) + "*" + "*".join(factors)
    else:
        body = str(c)
    return ("+" if coefficient >= 0 else "-") + body


def render(directory, check=False):
    equation = json.loads((directory / "equation.json").read_text())
    n, m = len(equation["variables"]), len(equation["residuals"])
    text_lines = [f"Domain: Z^{n}. Equation: sum(r_j^2, j=0,...,{m-1}) = 0.", ""]
    tex_lines = ["% Generated exactly from the adjacent equation.json.",
                 "\\begingroup\\small", "\\allowdisplaybreaks[4]", "\\begin{align*}"]
    for j, row in enumerate(equation["residuals"]):
        plain = " ".join(term(c, mon) for c, mon in row["terms"])
        text_lines.append(f"r_{j} = {plain.lstrip('+')}    # {row['label']}")
        atoms = [term(c, mon, True) for c, mon in row["terms"]]
        if atoms:
            atoms[0] = atoms[0].lstrip("+")
        chunks, current, width = [], [], 0
        for atom in atoms:
            # Weight rendered mathematical glyphs rather than TeX markup.
            cost = len(atom.replace("_{", "").replace("^{", "").replace("}", "")) + 1
            if current and width + cost > 66:
                chunks.append(" ".join(current)); current, width = [], 0
            current.append(atom); width += cost
        if current:
            chunks.append(" ".join(current))
        for k, chunk in enumerate(chunks):
            prefix = "r_{" + str(j) + "} &={}" if k == 0 else "&{}"
            ending = " \\\\" if (j != m - 1 or k != len(chunks) - 1) else ""
            tex_lines.append(prefix + chunk + ending)
    tex_lines.extend(["\\end{align*}", "\\endgroup", ""])
    translation = json.loads((directory / "translation_certificate.json").read_text())
    projection = json.loads((directory / "projection_certificate.json").read_text())
    shifts = dict(translation["shifts"])
    source_indices = projection["retained_original_variables"]
    variable_lines = ["index\tvariable\tsource_index\tsource_name\tkind\tsource_equals_variable_plus_shift"]
    variable_lines.extend(f"{i}\tx{i}\t{source_indices[i]}\t{v['name']}\t{v.get('kind','')}\t{shifts.get(i,0)}"
                          for i, v in enumerate(equation["variables"]))
    outputs = {"residuals.txt": "\n".join(text_lines) + "\n",
               "residuals.tex": "\n".join(tex_lines),
               "variables.tsv": "\n".join(variable_lines) + "\n"}
    for name, value in outputs.items():
        path = directory / name
        if check:
            if not path.exists() or path.read_text() != value:
                raise ValueError("transcription mismatch: " + name)
        else:
            path.write_text(value)
    return {"variables": n, "residuals": m, "files": list(outputs)}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("directory", nargs="?", type=Path, default=ROOT / "equations/symmetric_caps")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    print(json.dumps(render(args.directory, args.check), sort_keys=True))
