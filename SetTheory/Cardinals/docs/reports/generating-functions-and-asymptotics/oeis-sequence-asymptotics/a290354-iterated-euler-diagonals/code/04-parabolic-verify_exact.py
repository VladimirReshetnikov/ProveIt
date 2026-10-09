"""Exact finite checks for the parabolic amplitude companion.

These checks verify normalizations and algebra; no finite computation proves
the asymptotic theorems. Standard-library arithmetic is used for counts.
SymPy is needed only for the four-term Fatou-coordinate residual.
"""

import argparse
import json
from fractions import Fraction
from math import comb, factorial
from pathlib import Path


def stirling_table(nmax):
    s = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    s[0][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            s[n][k] = s[n - 1][k - 1] + k * s[n - 1][k]
    return s


def bell_depths(nmax, mmax, s):
    current = [0] * (nmax + 1)
    current[1] = 1
    rows = [current]
    for _ in range(mmax):
        current = [0] + [sum(s[n][k] * current[k]
                             for k in range(1, n + 1))
                         for n in range(1, nmax + 1)]
        rows.append(current)
    return rows


def chain_polynomials(nmax, s):
    z = [[0], [1]]
    for n in range(2, nmax + 1):
        row = [0] * n
        for k in range(1, n):
            for j, c in enumerate(z[k]):
                row[j + 1] += s[n][k] * c
        z.append(row)
    return z


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    s = stirling_table(24)
    h = bell_depths(24, 40, s)
    z = chain_polynomials(24, s)
    majorants = 0
    for n in range(1, 25):
        for m in range(1, 41):
            bound = factorial(n) * Fraction(m, 2)**(n - 1)
            check(h[m][n] <= bound, f"majorant n={n},m={m}")
            majorants += 1

    finite_differences = 0
    for n in range(1, 25):
        differences = [h[m][n] for m in range(n + 1)]
        coefficients = []
        while differences:
            coefficients.append(differences[0])
            differences = [b - a for a, b in zip(differences,
                                                differences[1:])]
        check(coefficients[:-1] == z[n], f"chain coefficients n={n}")
        check(coefficients[-1] == 0, f"depth polynomial degree n={n}")
        for m in [0, 1, 2, 7, 20, 40]:
            value = sum(c * comb(m, k) for k, c in enumerate(z[n])
                        if k <= m)
            check(value == h[m][n], f"Newton expansion n={n},m={m}")
            finite_differences += 1

    # The exact geometric mixture follows from the binomial-basis identity.
    mixtures = 0
    for q in [Fraction(1, 2), Fraction(1), Fraction(2), Fraction(3, 2)]:
        a = q / (q + 1)
        for n in range(1, 25):
            direct = sum(Fraction(c) * q**k for k, c in enumerate(z[n]))
            mixture = (1 - a) * sum(Fraction(c) * a**k / (1-a)**(k+1)
                                    for k, c in enumerate(z[n]))
            check(direct == mixture, f"geometric mixture n={n},q={q}")
            mixtures += 1

    import sympy as sp
    w = sp.symbols("w")
    f = sp.exp(w) - 1
    a = [-sp.Rational(1, 36), sp.Rational(1, 540),
         sp.Rational(1, 7776), -sp.Rational(71, 435456)]
    defect = -2/f + 2/w + sp.log(f/w)/3 - 1
    defect += sum(a[j-1] * (f**j-w**j) for j in range(1, 5))
    residual = sp.series(defect, w, 0, 6).removeO().expand()
    check(residual == 0, "Fatou coefficient residual through degree five")

    result = {
        "status": "all exact finite checks passed",
        "scope": "normalizations and finite algebra; not asymptotic proof",
        "majorant_cases": majorants,
        "newton_evaluation_cases": finite_differences,
        "geometric_mixture_cases": mixtures,
        "fatou_residual_through_degree": 5,
        "first_chain_counts": [sum(z[n]) for n in range(1, 11)],
        "bell_diagonal_n1_to_n8": [h[n][n] for n in range(1, 9)],
    }
    out = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(out, encoding="utf-8")
    print(out, end="")


if __name__ == "__main__":
    main()
