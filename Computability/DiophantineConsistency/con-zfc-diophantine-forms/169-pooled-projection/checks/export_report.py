#!/usr/bin/env python3
"""Print literal residuals and reproducible metrics from the final equations."""
from pathlib import Path
from collections import Counter
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]

def term_text(coefficient, monomial, first=False, tex=True):
    c = abs(coefficient)
    sign = "-" if coefficient < 0 else ("" if first else "+")
    factors = []
    for i, power in sorted(Counter(monomial).items()):
        factor = ("x_{" + str(i) + "}") if tex else ("x" + str(i))
        if power > 1:
            factor += ("^{" + str(power) + "}") if tex else ("^" + str(power))
        factors.append(factor)
    body = (str(c) if c != 1 or not monomial else "")
    if body and factors and not tex:
        body += "*"
    body += (r"\," if tex else "*").join(factors)
    return sign + body

def export():
    report = ROOT / "report"
    metrics = {}
    for n in (218, 216):
        e = json.loads((ROOT / "algebra" / f"equation{n}.json").read_text())
        metrics[n] = json.loads((ROOT / "algebra" / f"metrics{n}.json").read_text())
        lines = [f"P_{n}(x0,...,x{n-1}) = sum(R_j^2, j=0,...,{len(e['residuals'])-1}).",
                 f"Domain: all {n} independent coordinates are unrestricted integers.", ""]
        for j, row in enumerate(e["residuals"]):
            expression = " ".join(term_text(c, m, i == 0, False)
                                  for i, (c, m) in enumerate(row["terms"]))
            lines.append(f"R{j} = {expression}")
        (ROOT / "algebra" / f"residuals{n}.txt").write_text("\n".join(lines) + "\n")
        if n == 218:
            chunks = ["% Literal residual appendix. Generated from algebra/equation218.json."]
            for j, row in enumerate(e["residuals"]):
                rendered = [term_text(c, m, i == 0) for i, (c, m) in enumerate(row["terms"])]
                visual = [len(term_text(c, m, i == 0, False)) for i, (c, m) in enumerate(row["terms"])]
                wrapped, current, width = [], [], 0
                for t, w in zip(rendered, visual):
                    if current and width + w + 2 > 88:
                        wrapped.append(" ".join(current))
                        current, width = [], 0
                    current.append(t)
                    width += w + 2
                if current:
                    wrapped.append(" ".join(current))
                chunks.append(r"\begin{align*}")
                chunks.append("R_{" + str(j) + "} &= " + wrapped[0] +
                              (r" \\" if len(wrapped) > 1 else ""))
                for k, line in enumerate(wrapped[1:]):
                    chunks.append(r"&\quad {} " + line +
                                  (r" \\" if k < len(wrapped) - 2 else ""))
                chunks.append(r"\end{align*}")
            (report / "residuals218.tex").write_text("\n".join(chunks) + "\n")
    commands = []
    for n, prefix in [(218, "Main"), (216, "Few")]:
        for key, suffix in [("monomials", "Terms"), ("height", "Height"), ("row_height", "RowHeight")]:
            commands.append(r"\newcommand{\%s%s}{%s}" % (prefix, suffix, format(metrics[n][key], ",")))
    (report / "metrics.tex").write_text("\n".join(commands) + "\n")
    identities = []
    for label, path in [
        ("Pinned 242-coordinate source", "composition/157-linear-crt/source/equation.json"),
        ("Composed 223-coordinate parent", "algebra/parent223.json"),
        ("Principal residual system", "algebra/equation218.json"),
        ("Companion residual system", "algebra/equation216.json"),
        ("Principal collected quartic", "algebra/expanded218.json"),
        ("Companion collected quartic", "algebra/expanded216.json"),
    ]:
        digest = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        identities.append(r"\par\smallskip\noindent\begin{minipage}{\linewidth}" + "\n" +
                          r"\textbf{" + label + r".} SHA-256:" + "\n" +
                          r"\begin{quote}\small\ttfamily" + "\n" +
                          r"\nolinkurl{" + digest + "}\n" + r"\end{quote}" + "\n" +
                          r"\end{minipage}\par")
    (report / "identities.tex").write_text("\n".join(identities) + "\n")
    return {"status": "passed", "printed_rows": metrics[218]["rows"],
            "printed_terms": metrics[218]["residual_terms"]}

if __name__ == "__main__":
    print(json.dumps(export(), indent=2))
