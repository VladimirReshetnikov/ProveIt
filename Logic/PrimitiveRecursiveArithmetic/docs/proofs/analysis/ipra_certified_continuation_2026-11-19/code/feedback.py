#!/usr/bin/env python3
"""Exact-rational reference computations for finite weighted feedback.

These computations validate examples and algebraic identities. They are not
iPRA proof certificates or a universal primitive-recursive program evaluator.
"""
from fractions import Fraction as Q
from typing import Callable
import json


def mv(a, x):
    return [sum((v*t for v, t in zip(row, x)), Q(0)) for row in a]


def weighted_size(x, w):
    if len(x) != len(w) or any(v <= 0 for v in w):
        raise ValueError("Dimension mismatch or nonpositive weight")
    return max((abs(v)/t for v, t in zip(x, w)), default=Q(0))


def half_certificate(a, w):
    m = len(w)
    return (all(v > 0 for v in w)
            and len(a) == m and all(len(row) == m for row in a)
            and all(v >= 0 for row in a for v in row)
            and all(2*v <= t for v, t in zip(mv(a, w), w)))


def orbit(f: Callable, x, n):
    out = [list(x)]
    for _ in range(n):
        out.append(f(out[-1]))
    return out


def residual(f, x, w):
    return weighted_size([a-b for a, b in zip(f(x), x)], w)


def linear_neumann(a, b, n):
    """S_n b, where S_n=I+A+...+A^(n-1), by a fixed finite recurrence."""
    x = [Q(0) for _ in b]
    for _ in range(n):
        x = [u+v for u, v in zip(mv(a, x), b)]
    return x


def check_examples():
    # A cyclic matrix whose ordinary infinity-norm row maximum is 3.
    a = [[Q(0), Q(3)], [Q(1, 16), Q(0)]]
    w = [Q(8), Q(1)]
    assert half_certificate(a, w)
    assert max(map(sum, a)) > 1
    b = [Q(1), Q(-2)]
    B = weighted_size(b, w)
    for n in range(16):
        sn = linear_neumann(a, b, n)
        apowb = list(b)
        for _ in range(n):
            apowb = mv(a, apowb)
        # Exact residual identity, with no approximation.
        assert [x-y for x, y in zip(sn, mv(a, sn))] == [x-y for x, y in zip(b, apowb)]
        assert weighted_size(apowb, w) <= B / 2**n
        snj = linear_neumann(a, b, n+7)
        assert weighted_size([x-y for x, y in zip(snj, sn)], w) <= 2*B / 2**n

    # A nonlinear cyclic fixed-point equation on the invariant square [1,2]^2.
    def f(z):
        x, y = z
        return [1+y*y/4, 1+x*x/16]

    an = [[Q(0), Q(1)], [Q(1, 4), Q(0)]]
    wn = [Q(2), Q(1)]
    assert half_certificate(an, wn)
    run = orbit(f, [Q(1), Q(1)], 9)
    D = weighted_size([x-y for x, y in zip(run[1], run[0])], wn)
    assert D == Q(1, 8)
    for n, x in enumerate(run):
        assert all(1 <= v <= 2 for v in x)
        for k in range(n, len(run)):
            assert weighted_size([v-t for v, t in zip(run[k], x)], wn) <= 2*D/2**n
        if n+1 < len(run):
            assert weighted_size([v-t for v, t in zip(run[n+1], x)], wn) <= D/2**n

    # Finite residual comparison, independent of an already existing fixed point.
    for x in run[:6]:
        for y in run[:6]:
            assert weighted_size([v-t for v, t in zip(x,y)], wn) <= 2*(residual(f,x,wn)+residual(f,y,wn))

    perturb = Q(1, 1024)
    def g(z):
        u = f(z)
        return [u[0]-perturb, u[1]]
    other = orbit(g, [Q(1), Q(1)], 8)[-1]
    assert all(1 <= v <= 2 for v in other)
    x = run[8]
    delta = perturb/wn[0]
    compare = 2*(residual(f,x,wn)+residual(g,other,wn)+delta)
    assert weighted_size([v-t for v,t in zip(x,other)], wn) <= compare

    # Degenerate dimension and a rejected noncontractive certificate.
    assert half_certificate([], [])
    assert linear_neumann([], [], 10) == []
    assert not half_certificate([[Q(1)]], [Q(1)])
    return {
        "status": "all exact-rational checks passed",
        "linear_cyclic_matrix": [[str(v) for v in row] for row in a],
        "linear_weights": [str(v) for v in w],
        "linear_checks": 16,
        "nonlinear_map": ["1+y^2/4", "1+x^2/16"],
        "nonlinear_domain": "[1,2]^2",
        "nonlinear_weights": [str(v) for v in wn],
        "initial_weighted_step": str(D),
        "iteration_8_decimal_for_orientation_only": [float(v) for v in x],
        "iteration_8_coordinate_tail_bounds": [str(2*D*t/2**8) for t in wn],
        "iteration_8_weighted_residual": str(residual(f,x,wn)),
        "perturbation_size": str(perturb),
        "perturbed_output_comparison_bound": str(compare),
        "scope": "finite reference calculations; no Lean or iPRA checking claimed",
    }


if __name__ == "__main__":
    print(json.dumps(check_examples(), indent=2))
