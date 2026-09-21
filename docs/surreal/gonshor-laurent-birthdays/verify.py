#!/usr/bin/env python3
"""Exact finite checks accompanying the Laurent-series birthday article.

Python 3.9+, standard library only. No floating-point arithmetic is used in
mathematical checks. This is NOT a proof assistant: its sign-expansion engine
implements Gonshor's theorem; independent formulas and finite searches are
checked against that engine.

An ordinal below omega**omega is a tuple (a_0, ..., a_n), denoting
omega**n*a_n + ... + omega*a_1 + a_0. The empty tuple denotes zero.
A polynomial is a dict mapping dyadic Fraction exponents to Fraction
coefficients. Non-dyadic rational coefficients have birthday omega.
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
import random
import time
from datetime import datetime, timezone
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

Ordinal = Tuple[int, ...]
Polynomial = Dict[Fraction, Fraction]
F = Fraction
ZERO: Ordinal = ()
OMEGA: Ordinal = (0, 1)


def normalize(a: Iterable[int]) -> Ordinal:
    values = list(a)
    if any(not isinstance(v, int) or v < 0 for v in values):
        raise ValueError("Ordinal coefficients must be nonnegative integers")
    while values and values[-1] == 0:
        values.pop()
    return tuple(values)


def omega_monomial(exponent: int, coefficient: int = 1) -> Ordinal:
    if exponent < 0 or coefficient < 0:
        raise ValueError("Negative ordinal exponent or coefficient")
    return (0,) * exponent + (coefficient,) if coefficient else ZERO


def natural_add(a: Ordinal, b: Ordinal) -> Ordinal:
    return normalize((a[i] if i < len(a) else 0) +
                     (b[i] if i < len(b) else 0)
                     for i in range(max(len(a), len(b))))


def ordinary_add(a: Ordinal, b: Ordinal) -> Ordinal:
    if not b:
        return a
    degree = len(b) - 1
    return normalize(b[i] if i < degree else
                     (a[i] if i < len(a) else 0) +
                     (b[i] if i < len(b) else 0)
                     for i in range(max(len(a), len(b))))


def natural_multiply(a: Ordinal, b: Ordinal) -> Ordinal:
    if not a or not b:
        return ZERO
    result = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            result[i + j] += ai * bj
    return normalize(result)


def compare(a: Ordinal, b: Ordinal) -> int:
    ka, kb = (len(a), a[::-1]), (len(b), b[::-1])
    return (ka > kb) - (ka < kb)


def ordinal_text(a: Ordinal) -> str:
    parts = []
    for i in range(len(a) - 1, -1, -1):
        c = a[i]
        if not c:
            continue
        base = "1" if i == 0 else ("omega" if i == 1 else "omega^%d" % i)
        parts.append(str(c) if i == 0 else base + ("*%d" % c if c != 1 else ""))
    return " + ".join(parts) or "0"


def is_dyadic(q: Fraction) -> bool:
    denominator = q.denominator
    return denominator & (denominator - 1) == 0


def real_birthday(q: Fraction) -> Ordinal:
    if not q:
        return ZERO
    if not is_dyadic(q):
        return OMEGA
    q = abs(q)
    h = q.denominator.bit_length() - 1
    ceiling = (q.numerator + q.denominator - 1) // q.denominator
    return (ceiling + h,)


@lru_cache(maxsize=None)
def dyadic_signs(q: Fraction) -> Tuple[int, ...]:
    """Return the actual finite sign sequence of a dyadic rational."""
    if not is_dyadic(q):
        raise ValueError("Only dyadic exponents have finite sign sequences")
    if q < 0:
        return tuple(-s for s in dyadic_signs(-q))
    if q == 0:
        return ()
    if q.denominator == 1:
        return (1,) * q.numerator
    integer_part = q.numerator // q.denominator
    result = [1] * (integer_part + 1)
    value, step = F(integer_part + 1), F(1, 2)
    while value != q:
        sign = 1 if value < q else -1
        result.append(sign)
        value += sign * step
        step /= 2
    return tuple(result)


@lru_cache(maxsize=None)
def reduced_block_birthday(signs: Tuple[int, ...], coefficient: Fraction) -> Ordinal:
    """Length of a term block after exponent-sign deletion.

    This implements the general finite-sign expansion rule, not the special
    closed Laurent formula. Signs of coefficients do not affect length.
    """
    if not coefficient:
        raise ValueError("A normal-form term must have nonzero coefficient")
    length: Ordinal = (1,)
    pluses = 0
    for sign in signs:
        if sign not in (-1, 1):
            raise ValueError("Signs must be -1 or +1")
        length = ordinary_add(length, omega_monomial(pluses + 1))
        if sign == 1:
            pluses += 1
    if is_dyadic(coefficient):
        remainder = len(dyadic_signs(abs(coefficient))) - 1
        length = ordinary_add(length, omega_monomial(pluses, remainder))
    else:
        # Removing the first sign from an omega-long real expansion leaves
        # order type omega; repeating each sign omega**pluses times adds
        # omega**(pluses+1) signs.
        length = ordinary_add(length, omega_monomial(pluses + 1))
    return length


def sign_birthday(poly: Polynomial) -> Ordinal:
    """Exact length by Gonshor's two deletion rules and concatenation."""
    items = sorted(((e, c) for e, c in poly.items() if c), reverse=True)
    seen_minus_prefixes = set()
    previous: Optional[Tuple[Tuple[int, ...], Fraction]] = None
    length = ZERO
    for exponent, coefficient in items:
        signs = dyadic_signs(exponent)
        reduced = []
        for i, sign in enumerate(signs):
            prefix = signs[:i + 1]
            delete = sign == -1 and prefix in seen_minus_prefixes
            if (sign == -1 and previous is not None and
                    not is_dyadic(previous[1]) and signs[:i] == previous[0]):
                delete = True
            if not delete:
                reduced.append(sign)
        length = ordinary_add(length, reduced_block_birthday(tuple(reduced), coefficient))
        seen_minus_prefixes.update(signs[:i + 1]
                                   for i, sign in enumerate(signs) if sign == -1)
        previous = (signs, coefficient)
    return length


def laurent_formula(poly: Polynomial) -> Ordinal:
    """Independent closed formula proved in the article; integer exponents."""
    poly = {e: c for e, c in poly.items() if c}
    if any(e.denominator != 1 for e in poly):
        raise ValueError("The Laurent formula requires integer exponents")
    positive_length = ZERO
    for e, c in poly.items():
        if e > 0:
            term = natural_multiply(omega_monomial(int(e)), real_birthday(c))
            positive_length = natural_add(positive_length, term)
    negative = [e for e in poly if e < 0]
    if not negative:
        return natural_add(positive_length, real_birthday(poly.get(F(0), F(0))))
    last = min(negative)
    m, coefficient = -int(last), poly[last]
    if not is_dyadic(coefficient):
        tail = (0, m + 1)
    else:
        predecessor = poly.get(last + 1, F(0))
        epsilon = int(not is_dyadic(predecessor))
        tail = (real_birthday(coefficient)[0] - 1 + epsilon, m)
    return ordinary_add(positive_length, tail)


def multiply(a: Polynomial, b: Polynomial) -> Polynomial:
    result: Polynomial = {}
    for e, c in a.items():
        for f, d in b.items():
            result[e + f] = result.get(e + f, F(0)) + c * d
    return {e: c for e, c in result.items() if c}


def polynomial_record(poly: Polynomial) -> List[List[str]]:
    return [[str(e), str(c)] for e, c in sorted(poly.items(), reverse=True) if c]


def ensure(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)


def check_pair(a: Polynomial, b: Polynomial) -> bool:
    ba, bb = sign_birthday(a), sign_birthday(b)
    actual = sign_birthday(multiply(a, b))
    bound = natural_multiply(ba, bb)
    ensure(compare(actual, bound) <= 0, json.dumps({
        "failure": "product bound", "a": polynomial_record(a),
        "b": polynomial_record(b), "actual": actual, "bound": bound}))
    return actual == bound


def regression_tests() -> dict:
    examples = [
        ({}, ZERO),
        ({F(0): F(-3, 4)}, (3,)),
        ({F(0): F(1, 3)}, OMEGA),
        ({F(1): F(1), F(0): F(-1)}, (1, 1)),
        ({F(1): F(1), F(1, 2): F(1)}, (0, 0, 1)),
        ({F(0): F(1), F(-1): F(1)}, OMEGA),
        ({F(0): F(1, 3), F(-1): F(1)}, (1, 1)),
        ({F(0): F(1, 3), F(-2): F(1)}, (0, 2)),
        ({F(-1): F(1, 3), F(-2): F(1, 2)}, (2, 2)),
        ({F(-1): F(1, 3), F(-3): F(1, 2)}, (1, 3)),
        ({F(1): F(1), F(-1): F(1)}, (0, 2)),
        ({F(2): F(1, 3), F(1): F(2), F(-2): F(3, 4)}, (2, 4, 0, 1)),
    ]
    for p, expected in examples:
        ensure(sign_birthday(p) == expected, "Regression: %r" % polynomial_record(p))
    ensure(ordinary_add((0, 1), (0, 0, 1)) == (0, 0, 1), "Ordinal absorption")
    ensure(natural_add((0, 1), (0, 0, 1)) == (0, 1, 1), "Natural sum")
    ensure(natural_multiply((3, 2), (4, 1)) == (12, 11, 2), "Natural product")
    for denominator in (1, 2, 4, 8, 16):
        for numerator in range(-40, 41):
            q = F(numerator, denominator)
            ensure(real_birthday(q) == normalize([len(dyadic_signs(q))]),
                   "Dyadic length formula")
    return {"status": "passed", "named_examples": len(examples),
            "dyadic_length_checks": 405, "ordinal_arithmetic_checks": 3}


def exhaustive_formula_check() -> dict:
    exponents = tuple(F(i) for i in range(-3, 3))
    coefficients = (F(0), F(1), F(-1), F(1, 2), F(2), F(1, 3), F(-1, 3))
    count = 0
    for row in itertools.product(coefficients, repeat=len(exponents)):
        p = dict(zip(exponents, row))
        actual, expected = sign_birthday(p), laurent_formula(p)
        ensure(actual == expected, json.dumps({"failure": "Laurent formula",
               "polynomial": polynomial_record(p), "sign": actual, "formula": expected}))
        count += 1
    return {"status": "passed", "polynomials": count,
            "exponents": [str(e) for e in exponents],
            "coefficient_choices": [str(c) for c in coefficients]}


def exhaustive_product_check() -> dict:
    exponents = tuple(F(i) for i in (-1, 0, 1))
    coefficients = (F(0), F(1), F(-1), F(1, 2), F(1, 3))
    polynomials = [dict(zip(exponents, row)) for row in
                   itertools.product(coefficients, repeat=len(exponents))]
    equalities, strict_tail_checks = 0, 0
    for a in polynomials:
        for b in polynomials:
            equality = check_pair(a, b)
            equalities += equality
            ac, bc = ({e: c for e, c in p.items() if c} for p in (a, b))
            if (any(e < 0 for e in ac) and bc and
                    bc not in ({F(0): F(1)}, {F(0): F(-1)})):
                ensure(not equality, "Strict finite Laurent bound")
                strict_tail_checks += 1
    return {"status": "passed", "polynomials": len(polynomials),
            "ordered_pairs": len(polynomials) ** 2,
            "equalities": equalities, "strict_tail_checks": strict_tail_checks,
            "exponents": [str(e) for e in exponents],
            "coefficient_choices": [str(c) for c in coefficients]}


def random_dyadic_check(count: int, seed: int) -> dict:
    rng = random.Random(seed)
    exponents = [F(i, 8) for i in range(-24, 25)]
    # Preserve these repeated values and their order for exact reproducibility.
    coefficients = [F(i, j) for j in (1, 2, 4, 3, 5)
                    for i in (-3, -2, -1, 1, 2, 3)]
    equalities = 0
    for _ in range(count):
        a = {e: rng.choice(coefficients) for e in
             rng.sample(exponents, rng.randint(1, 7))}
        b = {e: rng.choice(coefficients) for e in
             rng.sample(exponents, rng.randint(1, 7))}
        equalities += check_pair(a, b)
    return {"status": "passed", "pairs": count, "equalities": equalities,
            "seed": seed, "exponents": "i/8 for -24 <= i <= 24",
            "terms_per_factor": "uniformly 1 through 7; distinct exponents",
            "coefficient_sampling_list": [str(c) for c in coefficients],
            "interpretation": "Finite evidence beyond the integer-exponent theorem, not a proof"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--random-pairs", type=int, default=100000)
    parser.add_argument("--seed", type=int, default=394230)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    parser.add_argument("--quick", action="store_true", help="Regressions and 1000 random pairs only")
    args = parser.parse_args()
    if args.random_pairs < 0:
        parser.error("--random-pairs must be nonnegative")
    start = time.perf_counter()
    results = {
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "arithmetic": "exact integers and fractions.Fraction",
        "scope": "Finite verification; not machine-checked proofs of the article's theorems",
        "regressions": regression_tests(),
    }
    if not args.quick:
        results["exhaustive_laurent_formula"] = exhaustive_formula_check()
        results["exhaustive_laurent_products"] = exhaustive_product_check()
    results["random_dyadic_products"] = random_dyadic_check(
        min(args.random_pairs, 1000) if args.quick else args.random_pairs, args.seed)
    results["elapsed_seconds"] = round(time.perf_counter() - start, 3)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
