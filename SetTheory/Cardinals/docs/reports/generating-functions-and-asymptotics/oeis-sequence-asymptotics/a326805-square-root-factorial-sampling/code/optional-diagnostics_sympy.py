#!/usr/bin/env python3
"""Independent exact SymPy cross-check of orders 0..4 at modes 1 and 2.

The SymPy route expands the defining formal exponential directly, then
applies Fresnel moments. It does not reuse the standard-library generator's
Bernoulli recurrence, polynomial algebra, or exponential recurrence.
Run: python optional/diagnostics_sympy.py
Nothing is written unless --output PATH is supplied.
"""
import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))


def independently_derive(s, order, m):
    epsilon, v = s.symbols("epsilon v")
    alpha = s.Rational(1, 8 * m)
    beta = s.Rational(1, 2) - alpha
    logarithm = beta * s.log(1 + epsilon * v)
    for r in range(1, order + 1):
        logarithm -= ((-1) ** (r + 1) * s.bernoulli(r + 1, alpha) /
                      (r * (r + 1)) * (epsilon / (s.I * (1 + epsilon * v))) ** r)
    for r in range(2, order + 2):
        logarithm += s.I * (-1) ** (r - 1) * epsilon ** (r - 1) * v ** r / (r * (r - 1))
    logarithm = s.series(logarithm, epsilon, 0, order + 1).removeO()
    # Direct expansion of exp(log H); this deliberately differs from the
    # logarithmic-derivative recurrence in the standard-library implementation.
    H = s.series(s.exp(logarithm), epsilon, 0, order + 1).removeO().expand()
    answer = []
    for j in range(order + 1):
        result = s.Integer(0)
        for (power,), coefficient in s.Poly(H.coeff(epsilon, j), v).terms():
            if power % 2 == 0:
                r = power // 2
                moment = (-s.I / (4 * s.pi * m)) ** r * s.factorial2(2 * r - 1)
                result += coefficient * moment
        answer.append(s.expand(result))
    return answer


def run(order, modes):
    import sympy as s
    from exact_coefficients import coeffs

    rows = []
    for m in modes:
        independent = independently_derive(s, order, m)
        standard = coeffs(order, m)
        for j, (expression, polynomial) in enumerate(zip(independent, standard)):
            expected = sum((s.Rational(re.numerator, re.denominator) +
                            s.I * s.Rational(im.numerator, im.denominator)) / s.pi ** power
                           for power, (re, im) in polynomial.items())
            difference = s.simplify(expression - expected)
            rows.append({"mode_m": m, "order_j": j, "independent_expression": str(expression),
                         "exact_difference": str(difference), "equal": difference == 0})
    return {"kind": "independent_exact_symbolic_cross_check", "sympy_version": s.__version__,
            "floating_arithmetic_used": False,
            "qualification": "This exact finite algebra check validates coefficients only; "
                             "it does not establish analytic remainder estimates.",
            "all_exact_comparisons_pass": len(rows) == len(modes) * (order + 1) and all(row["equal"] for row in rows),
            "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=4, help="Largest coefficient order, 0..4 (default: 4)")
    parser.add_argument("--modes", type=int, nargs="+", default=[1, 2], help="Modes to compare, each 1..4")
    parser.add_argument("--output", type=Path, help="Also write JSON to this explicit path")
    args = parser.parse_args()
    try:
        if not 0 <= args.order <= 4:
            raise ValueError("--order must lie in 0..4; larger symbolic expansions are intentionally unsupported")
        if not all(1 <= m <= 4 for m in args.modes):
            raise ValueError("Every --modes value must lie in 1..4")
        result = run(args.order, args.modes)
        rendered = json.dumps(result, indent=2) + "\n"
        if args.output is not None:
            args.output.write_text(rendered, encoding="utf-8")
        print(rendered, end="")
        return 0 if result["all_exact_comparisons_pass"] else 1
    except (ImportError, OSError, ValueError, ArithmeticError) as exc:
        print(json.dumps({"status": "error", "message": str(exc)}))
        return 2


if __name__ == "__main__":
    sys.exit(main())
