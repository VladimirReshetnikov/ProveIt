#!/usr/bin/env python3
"""Regenerate the article's first-values table; standard library only."""
from pathlib import Path
from rueppel import binary_runs, parameter_coefficients


def polynomial(c0: int, c2: int) -> str:
    out = str(c0) if c0 else ""
    if c2:
        sign = "-" if c2 < 0 else ("+" if out else "")
        coefficient = "" if abs(c2) == 1 else str(abs(c2))
        out += sign + coefficient + "t^2"
    return out or "0"


def main() -> None:
    lines = [r"\begin{table}[H]", r"\centering\small",
             r"\renewcommand{\arraystretch}{1.1}",
             r"\begin{tabular}{@{}r c c r c l@{}}", r"\toprule",
             r"$n$ & Binary $n$ & Gray code $g(n)$ & $\Runs(n)$ & $\eps(n)$ & $H_n(f_t)$\\",
             r"\midrule"]
    for n in range(1, 17):
        g = n ^ (n >> 1)
        p = polynomial(*parameter_coefficients(n))
        lines.append(f"{n} & \\texttt{{{n:b}}} & \\texttt{{{g:b}}} & "
                     f"{binary_runs(n)} & {g & 1} & ${p}$" + r"\\")
    lines.extend([r"\bottomrule", r"\end{tabular}",
                  r"\caption{The first sixteen positive-order determinant polynomials. "
                  r"The sign and both coefficients are read from the index, not from a recurrence in the moments.}",
                  r"\label{tab:first}", r"\end{table}"])
    target = Path(__file__).resolve().parents[1] / "tables.tex"
    target.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Wrote {target}")


if __name__ == "__main__":
    main()
