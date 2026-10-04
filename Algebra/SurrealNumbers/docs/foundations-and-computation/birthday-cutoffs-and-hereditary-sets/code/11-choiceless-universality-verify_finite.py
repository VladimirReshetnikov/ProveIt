#!/usr/bin/env python3
"""Finite sanity checks for 'Surreal Universality Without Choice'.

Standard library only. These checks do NOT construct surreal fields, infinite
permutation models, or proofs over ZF/ZFA. They exercise finite interfaces used
in the mathematical proofs. In particular, finite chains are not simulations
of the ordered Mostowski model: their order automorphism groups are trivial.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import permutations, product
from pathlib import Path
import argparse
import json
import random
from typing import Iterable

Exponent = tuple[int, ...]
Polynomial = dict[Exponent, int]
SEED = 20261003


class Checks:
    def __init__(self) -> None:
        self.counts: dict[str, int] = defaultdict(int)

    def require(self, condition: bool, category: str, message: str) -> None:
        if not condition:
            raise AssertionError(f"{category}: {message}")
        self.counts[category] += 1


def encode_signs(signs: tuple[int, ...]) -> frozenset[int]:
    """-1 is minus; +1 is plus. Odd positions encode definedness."""
    if any(s not in (-1, 1) for s in signs):
        raise ValueError("Signs must be -1 or +1.")
    return frozenset({2 * i + 1 for i in range(len(signs))}
                     | {2 * i for i, s in enumerate(signs) if s == 1})


def decode_signs(code: frozenset[int]) -> tuple[int, ...]:
    if any(i < 0 for i in code):
        raise ValueError("A finite ordinal code cannot have negative entries.")
    defined = sorted(i // 2 for i in code if i % 2)
    if defined != list(range(len(defined))):
        raise ValueError("Defined coordinates must be an initial segment.")
    if any(i // 2 >= len(defined) for i in code):
        raise ValueError("Positive sign without a defined coordinate.")
    return tuple(1 if 2 * i in code else -1 for i in defined)


def ternary_to_binary(digits: tuple[int, ...]) -> tuple[int, ...]:
    blocks = ((0, 0), (0, 1), (1, 1))
    if any(d not in range(3) for d in digits):
        raise ValueError("Ternary digits must be 0, 1, or 2.")
    return tuple(bit for d in digits for bit in blocks[d])


def clean(p: Polynomial) -> Polynomial:
    return {m: c for m, c in p.items() if c}


def add(p: Polynomial, q: Polynomial) -> Polynomial:
    result = dict(p)
    for m, c in q.items():
        result[m] = result.get(m, 0) + c
    return clean(result)


def multiply(p: Polynomial, q: Polynomial) -> Polynomial:
    result: dict[Exponent, int] = defaultdict(int)
    for m, a in p.items():
        for n, b in q.items():
            if len(m) != len(n):
                raise ValueError("Incompatible numbers of variables.")
            result[tuple(x + y for x, y in zip(m, n))] += a * b
    return clean(dict(result))


def order_key(m: Exponent) -> Exponent:
    # Variable 0 is smallest. Largest variable of difference takes priority.
    return m[::-1]


def leading(p: Polynomial) -> tuple[Exponent, int]:
    if not p:
        raise ValueError("Zero has no leading monomial.")
    m = max(p, key=order_key)
    return m, p[m]


def sign_of_polynomial(p: Polynomial) -> int:
    if not p:
        return 0
    c = leading(p)[1]
    return 1 if c > 0 else -1


def random_polynomial(rng: random.Random, variables: int, terms: int = 6) -> Polynomial:
    p: dict[Exponent, int] = defaultdict(int)
    for _ in range(terms):
        m = tuple(rng.randrange(4) for _ in range(variables))
        p[m] += rng.randrange(-5, 6)
    return clean(dict(p))


def orbit_substitute(p: Polynomial, orbit: tuple[int, ...], count: int) -> Polynomial:
    result: dict[Exponent, int] = defaultdict(int)
    for m, c in p.items():
        if len(m) != len(orbit):
            raise ValueError("Orbit map does not match the variable set.")
        exponent = [0] * count
        for variable, degree in enumerate(m):
            exponent[orbit[variable]] += degree
        result[tuple(exponent)] += c
    return clean(dict(result))


def permute_variables(p: Polynomial, permutation: tuple[int, ...]) -> Polynomial:
    if sorted(permutation) != list(range(len(permutation))):
        raise ValueError("Not a permutation.")
    out: Polynomial = {}
    for m, c in p.items():
        n = [0] * len(m)
        for i, exponent in enumerate(m):
            n[permutation[i]] = exponent
        out[tuple(n)] = c
    return out


def evaluate(p: Polynomial, values: tuple[int, ...]) -> int:
    total = 0
    for m, coefficient in p.items():
        if len(m) != len(values):
            raise ValueError("Evaluation arity mismatch.")
        term = coefficient
        for x, degree in zip(values, m):
            term *= x ** degree
        total += term
    return total


def variable_difference(n: int, i: int, j: int) -> Polynomial:
    a, b = [0] * n, [0] * n
    a[i] = 1
    b[j] = 1
    return add({tuple(a): 1}, {tuple(b): -1})


def run_checks() -> dict[str, object]:
    checks = Checks()
    rng = random.Random(SEED)

    all_codes: set[frozenset[int]] = set()
    for length in range(10):
        for signs in product((-1, 1), repeat=length):
            code = encode_signs(signs)
            checks.require(decode_signs(code) == signs, "sign_codec", "Round trip failed")
            checks.require(code not in all_codes, "sign_codec", "Collision across lengths")
            all_codes.add(code)
        checks.require(len(all_codes) == 2 ** (length + 1) - 1,
                       "birthday_capacity", "Wrong finite birthday count")

    for length in range(7):
        source = list(product(range(3), repeat=length))
        target = [ternary_to_binary(d) for d in source]
        checks.require(all(len(t) == 2 * length for t in target),
                       "ternary_blocks", "Wrong encoded length")
        checks.require(len(set(target)) == len(source), "ternary_blocks", "Collision")
        for a, b in zip(target, target[1:]):
            checks.require(a < b, "ternary_blocks", "Lexicographic order not preserved")

    # Formal independent basis coordinates are sparse vector coordinates.
    # This checks the finite normal-form interface, not actual surreal values.
    label_positions = (3, 0, 4, 1)
    seen: set[Exponent] = set()
    for m in product(range(4), repeat=4):
        formal_E = [0] * 5
        for i, c in enumerate(m):
            formal_E[label_positions[i]] += c
        t = tuple(formal_E)
        checks.require(t not in seen, "formal_exponent_separation", "Exponent collision")
        seen.add(t)

    for _ in range(5000):
        m, n, shift = [tuple(rng.randrange(-5, 6) for _ in range(5)) for _ in range(3)]
        shifted_m = tuple(x + z for x, z in zip(m, shift))
        shifted_n = tuple(y + z for y, z in zip(n, shift))
        checks.require((order_key(m) < order_key(n)) ==
                       (order_key(shifted_m) < order_key(shifted_n)),
                       "ordered_exponents", "Translation invariance failed")

    for _ in range(1000):
        p, q = random_polynomial(rng, 4), random_polynomial(rng, 4)
        pq = multiply(p, q)
        if p and q:
            pm, pc = leading(p)
            qm, qc = leading(q)
            checks.require(leading(pq) == (tuple(a + b for a, b in zip(pm, qm)), pc * qc),
                           "leading_terms", "Leading-product identity failed")
            checks.require(sign_of_polynomial(pq) == sign_of_polynomial(p) * sign_of_polynomial(q),
                           "leading_terms", "Product sign failed")
            positive_p = p if pc > 0 else {m: -c for m, c in p.items()}
            positive_q = q if qc > 0 else {m: -c for m, c in q.items()}
            checks.require(sign_of_polynomial(add(positive_p, positive_q)) > 0,
                           "leading_terms", "Positive cone not additive")
        values = tuple(rng.randrange(-3, 4) for _ in range(4))
        checks.require(evaluate(pq, values) == evaluate(p, values) * evaluate(q, values),
                       "evaluation", "Multiplicativity failed")
        checks.require(evaluate(add(p, q), values) == evaluate(p, values) + evaluate(q, values),
                       "evaluation", "Additivity failed")

    n = 6
    for s in range(n):
        # Full finite symmetric-group analogue only. Tail is nonempty.
        stabilizer = [tuple(range(s)) + tail for tail in permutations(range(s, n))]
        observed_orbits = {frozenset(g[x] for g in stabilizer) for x in range(n)}
        expected_orbits = {frozenset({x}) for x in range(s)} | {frozenset(range(s, n))}
        checks.require(observed_orbits == expected_orbits, "finite_orbits", "Orbit classification failed")
        checks.require(len(observed_orbits) == s + 1, "finite_orbits", "Orbit count failed")
        orbit = tuple(i if i < s else s for i in range(n))
        qcount = s + 1
        for i in range(s, n):
            for j in range(s, n):
                difference = variable_difference(n, i, j)
                checks.require(not orbit_substitute(difference, orbit, qcount),
                               "orbit_kernel", "A same-orbit difference survived")
        for _ in range(8):
            p, q = random_polynomial(rng, n), random_polynomial(rng, n)
            mapped_p = orbit_substitute(p, orbit, qcount)
            mapped_q = orbit_substitute(q, orbit, qcount)
            checks.require(orbit_substitute(multiply(p, q), orbit, qcount) == multiply(mapped_p, mapped_q),
                           "orbit_quotient", "Quotient multiplicativity failed")
            checks.require(orbit_substitute(add(p, q), orbit, qcount) == add(mapped_p, mapped_q),
                           "orbit_quotient", "Quotient additivity failed")
            for g in stabilizer:
                checks.require(orbit_substitute(permute_variables(p, g), orbit, qcount) == mapped_p,
                               "orbit_invariance", "Stabilizer invariance failed")

    return {
        "status": "PASS",
        "seed": SEED,
        "assertions_passed": sum(checks.counts.values()),
        "categories": dict(sorted(checks.counts.items())),
        "scope": "Finite exact checks of encoding and algebraic interfaces only.",
        "not_checked": [
            "Theorems over all ordinals or arbitrary sets",
            "Real closedness of the surreal field",
            "Existence or internal semantics of infinite permutation models",
            "Historical novelty or publication priority",
            "Lean or Rocq formalization",
        ],
        "ordered_model_warning": (
            "No finite-chain automorphism test is used as a model of Aut(Q,<). "
            "The interval-orbit theorem is proved mathematically in the article."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("verification_results.json"))
    args = parser.parse_args()
    result = run_checks()
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
