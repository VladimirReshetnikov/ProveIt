#!/usr/bin/env python3
"""Exact finite checks for the accompanying research article.

These checks are not proofs of the arbitrary-support or infinite-family
results. Requires Python >= 3.10 and SymPy >= 1.12. No network access,
floating-point tests, or nonstandard computer-algebra service is used.

Run: python verify.py --output verification_results.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import platform
import random
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Any

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("Install the dependency with: python -m pip install sympy") from exc

SEED = 20260922
records: list[dict[str, Any]] = []


def record(category: str, name: str, ok: bool, **details: Any) -> None:
    records.append({"category": category, "name": name, "passed": bool(ok), **details})
    if not ok:
        raise AssertionError(f"Failed: {category} / {name}")


def falling_half(j: int) -> sp.Rational:
    return sp.prod(sp.Rational(1, 2) - i for i in range(j))


def check_mixed_differences() -> None:
    rng = random.Random(SEED)
    for dimension in range(1, 4):
        xs = sp.symbols(f"x0:{dimension}")
        for degree in range(1, 6):
            for trial in range(3):
                # One nonzero degree-D term, plus only lower-degree terms.
                polynomial = xs[0] ** degree
                for _ in range(10):
                    exponents = [0] * dimension
                    for _ in range(rng.randrange(degree)):
                        exponents[rng.randrange(dimension)] += 1
                    monomial = sp.prod(x ** e for x, e in zip(xs, exponents))
                    polynomial += rng.randint(-4, 4) * monomial
                # Add additional top-degree terms without cancelling x0**D.
                if dimension > 1:
                    polynomial += 2 * xs[-1] ** degree
                polynomial = sp.expand(polynomial)
                vectors = [
                    tuple(sp.Integer(rng.randint(-3, 3)) for _ in xs)
                    for _ in range(degree)
                ]
                top = sum(
                    coefficient * sp.prod(x ** e for x, e in zip(xs, powers))
                    for powers, coefficient in sp.Poly(polynomial, *xs).terms()
                    if sum(powers) == degree
                )
                difference = polynomial
                directional = top
                for vector in vectors:
                    substitutions = {x: x + u for x, u in zip(xs, vector)}
                    difference = sp.expand(
                        difference.subs(substitutions, simultaneous=True) - difference
                    )
                    directional = sp.expand(
                        sum(u * sp.diff(directional, x) for x, u in zip(xs, vector))
                    )
                record(
                    "mixed_difference", f"d{dimension}_D{degree}_trial{trial}",
                    sp.expand(difference - directional) == 0,
                    dimension=dimension, degree=degree,
                )
    # An additional identity retaining symbolic step sizes and the (-2)^D factor.
    x, y, b1, b2, b3 = sp.symbols("x y b1 b2 b3")
    p = x**3 + 2*x*y**2 + y**3 + x*y + 7
    top = x**3 + 2*x*y**2 + y**3
    directions = [(1, 0), (1, 2), (-2, 1)]
    current, derivative = p, top
    for b, v in zip((b1, b2, b3), directions):
        current = sp.expand(current.subs(
            {x: x - 2*b*v[0], y: y - 2*b*v[1]}, simultaneous=True) - current)
        derivative = sp.expand(v[0]*sp.diff(derivative, x) + v[1]*sp.diff(derivative, y))
    record("mixed_difference", "symbolic_sign_steps",
           sp.expand(current - (-2)**3*b1*b2*b3*derivative) == 0)


def check_multiquadratic() -> None:
    X = sp.Symbol("X")
    for count in range(1, 4):
        bs = sp.symbols(f"b0:{count}")
        As = sp.symbols(f"A0:{count}")
        orbit_product = sp.expand(sp.prod(
            X - sum(sign*b for sign, b in zip(signs, bs))
            for signs in itertools.product((-1, 1), repeat=count)
        ))
        even = True
        norm_poly = sp.Integer(0)
        for exponents, coefficient in sp.Poly(orbit_product, *bs).terms():
            even = even and all(e % 2 == 0 for e in exponents)
            norm_poly += coefficient * sp.prod(A ** (e//2) for A, e in zip(As, exponents))
        norm_poly = sp.expand(norm_poly)
        record("multiquadratic", f"sign_invariance_{count}", even)
        record("multiquadratic", f"degree_{count}", sp.degree(norm_poly, X) == 2**count)
        substituted = norm_poly.subs({A: b*b for A, b in zip(As, bs)}).subs(X, sum(bs))
        record("multiquadratic", f"annihilation_{count}", sp.expand(substituted) == 0)
        if count == 2:
            expected = (X**2-As[0]-As[1])**2-4*As[0]*As[1]
            record("multiquadratic", "two_root_quartic", sp.expand(norm_poly-expected) == 0)
    b, S, a, t = sp.symbols("b S a t")
    relation = sp.expand(((b+S)-S)**2-t*t*a)
    record("multiquadratic", "one_exception_relation",
           sp.rem(relation, b*b-t*t*a, b) == 0)
    # Square-class witnesses for the first six primes (not an infinite proof).
    primes = [2, 3, 5, 7, 11, 13]
    for mask in range(1, 1 << len(primes)):
        value = math.prod(p for i, p in enumerate(primes) if mask & (1 << i))
        record("square_class_examples", f"subset_{mask}", math.isqrt(value)**2 != value)


def check_vandermonde_and_jets() -> None:
    for dimension in range(1, 10):
        for offset in (0, 5):
            ns = [offset + i*i + 1 for i in range(dimension)]
            matrix = sp.Matrix([[sp.Integer(n)**k for n in ns] for k in range(dimension)])
            expected = sp.prod(ns[j]-ns[i] for i in range(dimension) for j in range(i+1, dimension))
            record("vandermonde", f"dimension{dimension}_offset{offset}",
                   matrix.det(method="domain-ge") == expected)
    # Exact specialization z=0 of the analytic jet coefficient matrices.
    for J in range(4):
        for K in range(4):
            dimension = (J+1)*(K+1)
            for sampling in ("consecutive", "offset", "odd"):
                if sampling == "consecutive":
                    ns = list(range(1, dimension+1))
                elif sampling == "offset":
                    ns = list(range(8, dimension+8))
                else:
                    ns = [2*i+1 for i in range(dimension)]
                matrix = sp.Matrix([
                    [falling_half(j)*sp.Integer(n)**k/sp.Integer(-2**n)**j for n in ns]
                    for j in range(J+1) for k in range(K+1)
                ])
                determinant = matrix.det(method="domain-ge")
                record("mixed_jet_rank", f"J{J}_K{K}_{sampling}", determinant != 0,
                       rows=dimension, columns=dimension, specialization="z=0")


def check_derivatives_and_taylor() -> None:
    z = sp.Symbol("z")
    t = sp.Symbol("t", positive=True)
    for n in (1, 2, 5):
        h = sp.sqrt(1-z/sp.Integer(2)**n)
        for j in range(9):
            lhs = sp.diff(h, z, j)/h
            rhs = falling_half(j)/(z-2**n)**j
            record("analytic_derivatives", f"n{n}_j{j}", sp.simplify(lhs-rhs) == 0)
    for q in (sp.Integer(-3), sp.Integer(-1), sp.Integer(0), sp.Rational(1,2),
              sp.Integer(2), sp.Rational(5,3)):
        current = t**q
        for k in range(7):
            target = (-1)**k*sp.rf(q, k)*t**(q+k)
            record("BM_restriction", f"q{q}_k{k}", sp.simplify(current-target) == 0)
            current = sp.expand(-t*t*sp.diff(current, t))
    N = 8
    for j in range(9):
        finite = sp.expand(sum(
            sp.diff(sp.sqrt(1-z/sp.Integer(2)**n), z, j).subs(z, 0)*t**n
            for n in range(1, N+1)
        ))
        expected = sp.series((-1)**j*falling_half(j)*t/(2**j-t), t, 0, N+1).removeO()
        record("Taylor_identity", f"j{j}_through_t{N}", sp.expand(finite-expected) == 0)
    for N in (1, 2, 5, 8):
        finite_F = sum(t**n*sp.sqrt(1-z/sp.Integer(2)**n) for n in range(1, N+1))
        boundary = t*sp.sqrt(1-z)-t**(N+1)*sp.sqrt(1-z/sp.Integer(2)**N)
        result = sp.expand(finite_F.subs(z, 2*z)-t*finite_F-boundary)
        record("dilation_identity", f"finite_boundary_N{N}", sp.simplify(result) == 0)


def code(bits: tuple[int, ...]) -> int:
    if not bits or any(bit not in (0, 1) for bit in bits):
        raise ValueError("Expected a nonempty binary string")
    m = len(bits)
    return 2**m + sum(bit*2**(m-j-1) for j, bit in enumerate(bits))


def check_binary_prefixes() -> None:
    depth = 10
    seeds = list(itertools.product((0, 1), repeat=4))
    branches = {seed: tuple(seed[i % 4] for i in range(depth)) for seed in seeds}
    sets = {seed: {code(bits[:m]) for m in range(1, depth+1)} for seed, bits in branches.items()}
    for a, b in itertools.combinations(seeds, 2):
        ba, bb = branches[a], branches[b]
        common = 0
        for x, y in zip(ba, bb):
            if x != y:
                break
            common += 1
        expected = {code(ba[:m]) for m in range(1, common+1)}
        record("binary_prefixes", f"intersection_{''.join(map(str,a))}_{''.join(map(str,b))}",
               sets[a] & sets[b] == expected)
    for seed in seeds:
        others = set().union(*(sets[s] for s in seeds if s != seed))
        private = sets[seed] - others
        # From length four onward, every prefix is private among these branches.
        expected_private = {code(branches[seed][:m]) for m in range(4, depth+1)}
        record("binary_prefixes", f"private_{''.join(map(str,seed))}", private == expected_private)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    args = parser.parse_args()
    start = time.perf_counter()
    error: str | None = None
    tests = [check_mixed_differences, check_multiquadratic, check_vandermonde_and_jets,
             check_derivatives_and_taylor, check_binary_prefixes]
    try:
        for test in tests:
            before = len(records)
            test()
            print(f"{test.__name__}: {len(records)-before} checks passed", flush=True)
    except Exception as exc:
        error = f"{type(exc).__name__}: {exc}"
    counts = Counter(item["category"] for item in records)
    result = {
        "status": "passed" if error is None and all(r["passed"] for r in records) else "failed",
        "scope": "Finite exact examples and identities only; not a proof of the infinite theorems.",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "random_seed": SEED,
        "elapsed_seconds": round(time.perf_counter()-start, 3),
        "total_checks": len(records),
        "category_counts": dict(sorted(counts.items())),
        "error": error,
        "checks": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(f"{result['status']}: {len(records)} checks; output: {args.output}")
    if error:
        print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
