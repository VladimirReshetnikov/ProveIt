#!/usr/bin/env python3
"""Finite exact checks accompanying Maximal Transcendence in Hahn Joins.

These checks illustrate the finite algebraic mechanism. They do NOT verify
infinite Hahn supports, cardinal statements, or primality in the omnific rings.
Requires Python 3 and SymPy. No network access or external data are used.
"""
from __future__ import annotations

from itertools import combinations, product
import platform
import sys

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required: install it before running verify.py") from exc


def require(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)


def algebra_checks() -> None:
    x1, x2, x3, y1, y2, y3 = sp.symbols("x1 x2 x3 y1 y2 y3")
    xs = (x1, x2, x3)
    ys = (y1, y2, y3)
    u1 = x1 + x2 + x3
    u2 = x1 * x2 + x3**2
    v = sp.Matrix([x * sp.diff(u1, x) for x in xs])
    w = sp.Matrix([x * sp.diff(u2, x) for x in xs])
    cs = v.cross(w)
    expected = sp.Matrix([
        2*x2*x3**2-x1*x2*x3,
        x1*x2*x3-2*x1*x3**2,
        x1*x2*(x1-x2),
    ])
    require(all(sp.expand(a-b) == 0 for a, b in zip(cs, expected)),
            "The displayed cross product must be exact.")

    def deriv(expr: sp.Expr) -> sp.Expr:
        return sp.cancel(sum(c*x*sp.diff(expr, x) for c, x in zip(cs, xs)))

    require(deriv(u1) == 0 and deriv(u2) == 0, "Both generators must be killed.")
    quotient = (u1**2 + u2) / (u1 - 3*u2 + 1)
    require(deriv(quotient) == 0, "The generated rational expression must be killed.")
    mixed = sum(x*y for x, y in zip(xs, ys))
    image = sp.expand(deriv(mixed))
    require(image != 0, "The mixed derivative must survive.")
    numeric_x_image = image.subs({x1: 1, x2: 2, x3: 3})
    require(sp.expand(numeric_x_image - (30*y1 - 24*y2 - 6*y3)) == 0,
            "The displayed specialization must agree.")
    print("PASS: exact cross-product annihilator, two generators, quotient rule.")
    print("PASS: distinct-y mixed derivative remains nonzero.")
    print("      D(F) at x=(1,2,3):", numeric_x_image)


def trace_witness(xs: tuple[int, ...], bits: tuple[int, ...], n: int) -> tuple[int, set[int]]:
    """Return a distinguishing finite set s (bit mask) and its selected traces T."""
    s = 0
    for a, b in combinations(xs, 2):
        difference = a ^ b
        require(difference != 0, "Inputs must be distinct.")
        s |= difference & -difference
    require(s < 2**n, "The witness set must stay in the finite universe.")
    traces = [x & s for x in xs]
    require(len(set(traces)) == len(xs), "Traces must distinguish all inputs.")
    selected = {trace for trace, bit in zip(traces, bits) if bit}
    return s, selected


def incidence_checks() -> None:
    n = 4
    patterns = 0
    for r in range(1, 5):
        for xs in combinations(range(2**n), r):
            for bits in product((0, 1), repeat=r):
                s, selected = trace_witness(xs, bits, n)
                require(tuple(int((x & s) in selected) for x in xs) == bits,
                        "Every prescribed Boolean pattern must be realized.")
                patterns += 1
    print(f"PASS: {patterns:,} Boolean patterns (up to 4 sets on a 4-point universe).")
    print("      The extra xi coordinate in the infinite proof replicates each witness.")


def branch_codes(period: str, depth: int) -> set[int]:
    if not period or set(period) - {"0", "1"} or depth < 1:
        raise ValueError("Provide a nonempty binary period and positive depth.")
    value = 0
    result: set[int] = set()
    for m in range(1, depth + 1):
        value = 2*value + int(period[(m-1) % len(period)])
        result.add(2**m - 1 + value)
    return result


def branch_checks() -> None:
    periods = ("0", "1", "01", "001", "011", "0001", "0011", "0111")
    depth = 32
    branches = [branch_codes(p, depth) for p in periods]
    require(branch_codes("0", 4) == {1, 3, 7, 15}, "Zero-branch codes differ.")
    require(branch_codes("1", 4) == {2, 6, 14, 30}, "One-branch codes differ.")
    minimum = depth
    for j, branch in enumerate(branches):
        other_union = set().union(*(b for i, b in enumerate(branches) if i != j))
        count = len(branch - other_union)
        minimum = min(minimum, count)
        require(count >= 20, "The selected branches must have long exclusive tails.")
    print(f"PASS: {len(periods)} distinct periodic branches through depth {depth};")
    print(f"      minimum number of exclusive nodes: {minimum}.")


def exponent_orientation() -> None:
    # This is an orientation check only; monotonicity and the limit are proved
    # in the article, not established by floating-point experiments.
    primes = list(sp.primerange(1, 100))
    rho = [sp.Pow(primes[2*n], -sp.Rational(3, 2))
           + sp.Pow(primes[2*n+1], -sp.Rational(3, 2)) for n in range(10)]
    approximations = [float(r.evalf(30)) for r in rho]
    require(all(a > b > 0 for a, b in zip(approximations, approximations[1:])),
            "The initial exponent sequence must decrease positively.")
    print("PASS: first ten exponents have the analytically proved orientation.")
    print("      First four approximations:", ", ".join(f"{x:.10f}" for x in approximations[:4]))


def main() -> int:
    print("Finite verification for Maximal Transcendence in Hahn Joins")
    print(f"Python {platform.python_version()}; SymPy {sp.__version__}")
    print("=" * 65)
    algebra_checks()
    incidence_checks()
    branch_checks()
    exponent_orientation()
    print("=" * 65)
    print("All implemented finite checks passed.")
    print("Not a formal verification of infinite Hahn statements or omnific primality.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
