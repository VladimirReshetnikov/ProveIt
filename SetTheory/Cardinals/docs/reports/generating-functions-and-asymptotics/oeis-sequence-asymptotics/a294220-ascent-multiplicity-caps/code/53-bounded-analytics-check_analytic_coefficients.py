#!/usr/bin/env python3
"""Optional exact replay of printed sector coefficients and kappa_m (SymPy)."""
from __future__ import annotations

import ast
from pathlib import Path
import sys

from sector_coefficients import coefficients, f_coefficients, integer, kappa, s, y


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def same(actual, expected, context):
    require(actual == expected, f"{context}: got {actual!r}; expected {expected!r}")


def rejects(function, args, context):
    try:
        function(*args)
    except ValueError:
        return
    raise RuntimeError(f"{context}: invalid arguments were accepted")


def main():
    here = Path(__file__).resolve().parent
    for path in here.glob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        require(not any(isinstance(node, ast.Assert) for node in ast.walk(tree)),
                f"removable assertion statement in {path.name}")
    bad_cases = 0
    for bad in (0, -1, True, False, 1.0, "1", None):
        rejects(coefficients, (bad, 0), f"invalid m={bad!r}")
        rejects(kappa, (bad,), f"invalid kappa m={bad!r}")
        bad_cases += 2
    for bad in (-1, True, False, 0.0, "0", None):
        rejects(coefficients, (1, bad), f"invalid order={bad!r}")
        rejects(f_coefficients, (bad,), f"invalid f order={bad!r}")
        bad_cases += 2
    same(bad_cases, 26, "invalid-input coverage")
    expected_f = (1/(1-y), -y/(1-y)**3, y*(1+2*y)/(1-y)**5)
    for order, (actual, expected) in enumerate(zip(f_coefficients(2), expected_f)):
        same(s.cancel(actual-expected), 0, f"rational function f_{order}")
    expected = {
        1: [s.Integer(1), s.Integer(0), s.Integer(0), s.Integer(0)],
        2: [s.Integer(1), -s.Rational(31, 8), s.Rational(5437, 128), -s.Rational(896281, 1024)],
        3: [s.Integer(1), -s.Rational(43, 3), s.Rational(32791, 81), -s.Rational(40869055, 2187)],
    }
    for m, values in expected.items():
        actual = coefficients(m, 3)
        same(len(actual), 4, f"coefficient coverage m={m}")
        for order, value in enumerate(actual):
            require(value.is_Rational is True, f"c[{m},{order}] is not an exact rational")
        same(actual, values, f"printed rational coefficients m={m}, orders 0..3")
        same(coefficients(m, 0), values[:1], f"order-zero truncation m={m}")
        same(coefficients(m, 2), values[:3], f"truncation consistency m={m}")
        print(f"PASS m={m}, j=0..3: {actual}", flush=True)
    tested_m = (1, 2, 3, 4, 5, 8, 12)
    for m in tested_m:
        actual = coefficients(m, 1)
        same(actual[0], 1, f"leading coefficient m={m}")
        same(actual[1], kappa(m), f"first correction kappa_{m}")
        print(f"PASS kappa_{m} = {actual[1]}", flush=True)
    print(f"PASS exact optional analytic replay (SymPy {s.__version__}); 26 invalid-input checks", flush=True)
    print("Finite algebraic agreement does not prove asymptotic remainder estimates", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RuntimeError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
