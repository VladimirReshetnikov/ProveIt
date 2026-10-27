#!/usr/bin/env python3
"""Finite exact checks of scoped Hermite-loss and Newton-mode lemmas.
This tests algebraic identities/bounds, not SAT algorithms or ETH.
Uses explicit exceptions, not assert, so checks remain active under python -O.
"""
import argparse
import itertools
import json
import sys
from fractions import Fraction
from math import comb, factorial


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def losses(a, q):
    u = len(q)
    if not isinstance(a, int) or not (a >= u >= 1):
        raise ValueError("Require integer a >= len(q) >= 1.")
    if any(not isinstance(x, int) or x < 0 for x in q):
        raise ValueError("Require nonnegative integer profile entries.")
    padded = tuple(q) + (0,) * (a + 1 - u)
    return tuple(
        sum((Fraction(j, 2**j) * (padded[i] - padded[i+j])
             for j in range(1, a-i+1)), Fraction(0))
        for i in range(u)
    )


def check_guards():
    rejected = 0
    for a, q in [(0, (1,)), (3, ()), (2, (1, -1)), (2, (1, Fraction(1, 2)))]:
        try:
            losses(a, q)
        except ValueError:
            rejected += 1
        else:
            raise RuntimeError("Invalid taper input was accepted.")
    return rejected


def check_tapers(max_u=5, max_q=5):
    total = admissible = nonmonotone = 0
    weakest_margin = None
    for u in range(1, max_u+1):
        for a in range(u, u+3):
            L = 2**a
            for q in itertools.product(range(max_q+1), repeat=u):
                total += 1
                ell = losses(a, q)
                Q = max(q)
                require(max(ell) >= Fraction(Q, 2*u),
                        f"Profile-only lower bound failed: a={a}, q={q}, ell={ell}")
                # Positive loss cannot occur at a zero multiplicity.
                require(all(q[i] > 0 or ell[i] <= 0 for i in range(u)),
                        f"Retained-node check failed: a={a}, q={q}")
                degree_mass = L * sum((Fraction(q[i], 2**i)
                                       for i in range(u)), Fraction(0))
                for M in range(1, 4):
                    if degree_mass <= M*(2*L-1):
                        continue
                    admissible += 1
                    if any(q[i] < q[i+1] for i in range(u-1)):
                        nonmonotone += 1
                    candidates = [ell[i] for i in range(u) if q[i] > 0]
                    require(bool(candidates), "Degree condition with no retained node.")
                    margin = max(candidates) - Fraction(M, 4*u)
                    require(margin > 0,
                            f"Degree-conditioned bound failed: a={a}, M={M}, q={q}")
                    if weakest_margin is None or margin < weakest_margin:
                        weakest_margin = margin
    return {
        "profiles_checked": total,
        "degree_admissible_cases_checked": admissible,
        "nonmonotone_degree_admissible_cases": nonmonotone,
        "smallest_positive_margin": str(weakest_margin),
        "ranges": {"u": [1, max_u], "a": "u,u+1,u+2",
                   "q_entry": [0, max_q], "M": [1, 3]},
    }


def check_newton():
    checks = interpolation_checks = 0
    for A in [3, 5, 7, 9, 11]:
        for h in [2, 4, 8]:
            for b in range(8):
                denominator = 1
                for r in range(b+1):
                    denominator *= A-h*r
                if denominator == 0:
                    continue
                left = sum(((-1)**(b-r)*comb(b, r)*Fraction(1, A-h*r)
                            for r in range(b+1)), Fraction(0))
                right = Fraction(factorial(b)*h**b, denominator)
                require(left == right,
                        f"Forward-difference identity failed: {A,h,b}")
                checks += 1
            for d in range(1, 8):
                if any(A-h*r == 0 for r in range(d)):
                    continue
                diffs = []
                for b in range(d):
                    denominator = 1
                    for r in range(b+1):
                        denominator *= A-h*r
                    diffs.append(Fraction(factorial(b)*h**b, denominator))
                for j in range(d):
                    value = sum((comb(j, b)*diffs[b] for b in range(j+1)), Fraction(0))
                    require(value == Fraction(1, A-h*j),
                            f"Finite Newton interpolation failed: {A,h,d,j}")
                    interpolation_checks += 1
    return {"forward_difference_identities": checks,
            "finite_interpolation_values": interpolation_checks}


def integer_v2(value):
    if not isinstance(value, int) or value == 0:
        raise ValueError("2-adic valuation requires a nonzero integer.")
    value = abs(value)
    return (value & -value).bit_length()-1


def check_direct_grid_losses():
    """Compare the loss formula with products defining E_t(0), on small grids."""
    products = 0
    for a in range(1, 4):
        L = 2**a
        grid = range(-L, L)
        for u in range(1, a+1):
            for q in itertools.product(range(3), repeat=u):
                ell = losses(a, q)
                for t in grid:
                    if t == 0:
                        continue
                    i = integer_v2(t)
                    if i >= u or q[i] == 0:
                        continue
                    E = Fraction(1)
                    for node in grid:
                        if node in (0, t):
                            continue
                        level = integer_v2(node)
                        multiplicity = q[level] if level < u else 0
                        E *= Fraction(-node, t-node)**multiplicity
                    direct_loss = integer_v2(E.denominator)-integer_v2(E.numerator)
                    expected = Fraction(L, 2**i)*ell[i]
                    require(direct_loss == expected,
                            f"Direct grid-normalizer identity failed: {a,u,q,t}")
                    products += 1
    return {"rational_normalizer_products": products,
            "ranges": {"a": [1, 3], "u": "1,...,a", "q_entry": [0, 2]}}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    args = parser.parse_args()
    result = {
        "status": "passed",
        "python_optimization_level": sys.flags.optimize,
        "scope": "Exact finite arithmetic checks; not a SAT solver, proof assistant, or global complexity proof.",
        "guard_cases_rejected": check_guards(),
        "taper": check_tapers(),
        "newton": check_newton(),
        "direct_grid_loss": check_direct_grid_losses(),
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(text)
    print(text, end="")


if __name__ == "__main__":
    main()

