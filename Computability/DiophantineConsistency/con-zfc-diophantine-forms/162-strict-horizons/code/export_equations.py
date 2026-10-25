#!/usr/bin/env python3
"""Generate or check exact readable exports of the two fixed quartics."""
from pathlib import Path
from collections import Counter
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]


def signed_term(coefficient, monomial, latex=False):
    counts = Counter(monomial)
    factors = []
    for i, power in sorted(counts.items()):
        atom = ("x_{" + str(i) + "}") if latex else "x" + str(i)
        if power != 1:
            atom += ("^{" + str(power) + "}") if latex else "^" + str(power)
        factors.append(atom)
    separator = " " if latex else "*"
    body = separator.join(factors)
    c = abs(coefficient)
    if not body:
        body = str(c)
    elif c != 1:
        body = str(c) + separator + body
    return ("-" if coefficient < 0 else "+"), body


def plain_row(terms):
    parts = []
    for j, (coefficient, monomial) in enumerate(terms):
        sign, body = signed_term(coefficient, monomial)
        parts.append(("-" if sign == "-" else "") + body if j == 0
                     else " " + sign + " " + body)
    return "".join(parts) or "0"


def latex_row(index, terms):
    chunks = []
    chunk = ""
    width = 0
    for j, (coefficient, monomial) in enumerate(terms):
        sign, body = signed_term(coefficient, monomial, True)
        term = (("-" if sign == "-" else "") + body if j == 0
                else " " + sign + " " + body)
        weight = 3 + len(str(abs(coefficient))) + sum(
            2.6 + 0.65 * len(str(i)) + (1.5 if count > 1 else 0)
            for i, count in Counter(monomial).items())
        if chunk and width + weight > 97:
            chunks.append(chunk)
            chunk, width = term.lstrip(), weight
        else:
            chunk += term
            width += weight
    chunks.append(chunk or "0")
    body = "R_{" + str(index) + "} &={}" + chunks[0]
    for chunk in chunks[1:]:
        body += "\n" + r"\\ &\phantom{={}}" + chunk
    return "\\[\n\\begin{aligned}\n" + body + "\n\\end{aligned}\n\\]\n"


def exports(folder):
    equation = json.loads((folder / "equation.json").read_text())
    rows = equation["residuals"]
    n = len(equation["variables"])
    plain = ("Domain: unrestricted integers.\n"
             f"P(x0,...,x{n-1}) = sum(Rj^2, j=0,...,{len(rows)-1}).\n\n")
    plain += "\n".join(f"R{i} = {plain_row(r['terms'])}"
                       for i, r in enumerate(rows)) + "\n"
    tex = ("% Generated from equation.json; do not edit independently.\n"
           "\\begingroup\n\\small\n"
           "\\setlength{\\abovedisplayskip}{4pt}\n"
           "\\setlength{\\belowdisplayskip}{4pt}\n")
    tex += "".join(latex_row(i, r["terms"]) for i, r in enumerate(rows))
    tex += "\\endgroup\n"
    variables = "index\tname_in_source_provenance\tkind\n" + "".join(
        f"{i}\t{v['name']}\t{v['kind']}\n"
        for i, v in enumerate(equation["variables"]))
    return {"residuals.txt": plain, "residuals.tex": tex,
            "variables.tsv": variables}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    checked = []
    for name in ("principal236", "dense235"):
        folder = ROOT / "direct" / name
        for filename, data in exports(folder).items():
            target = folder / filename
            if args.check:
                if not target.exists() or target.read_bytes() != data.encode():
                    raise ValueError("Readable export differs: " + str(target))
            else:
                target.write_text(data)
            checked.append(str(target.relative_to(ROOT)))
    source = ROOT / "direct/principal236/residuals.tex"
    target = ROOT / "report/residuals.tex"
    if args.check:
        if target.read_bytes() != source.read_bytes():
            raise ValueError("Report appendix differs from principal")
    else:
        target.write_bytes(source.read_bytes())
    checked.append(str(target.relative_to(ROOT)))
    print(json.dumps({"status": "PASS", "exact_readable_exports": checked}, indent=2))


if __name__ == "__main__":
    main()
