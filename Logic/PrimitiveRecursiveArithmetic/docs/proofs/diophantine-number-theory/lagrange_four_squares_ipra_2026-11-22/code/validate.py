#!/usr/bin/env python3
"""Reproduce the exact-arithmetic checks distributed with the proof packet.

These finite and symbolic checks corroborate implementation details. They do
not replace the universal iPRA proof, and they do not compile the Lean files.
"""

from __future__ import annotations

import json
from collections import defaultdict
from itertools import product
from pathlib import Path
import sys

from four_squares import (
    State, bounded_reference, centered, conj, four_squares, is_prime,
    mul, norm, prime_rep, prime_trace, seed, step,
)


def symbolic_checks() -> dict:
    import sympy as sp
    x = sp.symbols("a b c d")
    y = sp.symbols("e f g h")
    euler = sp.expand(norm(mul(x, y)) - norm(x) * norm(y))
    diagonal = tuple(sp.expand(v) for v in mul(x, conj(x)))
    assert euler == 0
    assert diagonal == (norm(x), 0, 0, 0)
    a, b, c, d = x
    half = ((a + b) / 2, (a - b) / 2, (c + d) / 2, (c - d) / 2)
    assert sp.expand(2 * norm(half) - norm(x)) == 0
    return {"sympy_version": sp.__version__, "euler_polynomial_remainder": "0",
            "conjugate_product": "(norm(x),0,0,0)", "halving_polynomial_remainder": "0"}


def exhaustive_descent_states() -> dict:
    primes = (2, 3, 5, 7, 11, 13)
    counts = {"terminal": 0, "even-halving": 0, "odd-centered": 0}
    by_prime = {}
    for p in primes:
        pairs = defaultdict(list)
        for a, b in product(range(1 - p, p), repeat=2):
            pairs[a * a + b * b].append((a, b))
        count = 0
        for m in range(1, p):
            target = m * p
            for subtotal, lefts in pairs.items():
                for a, b in lefts:
                    for c, d in pairs.get(target - subtotal, ()):
                        x = a, b, c, d
                        s = State(m, x)
                        t = step(s)
                        assert norm(x) == m * p
                        assert 1 <= t.m < p
                        assert norm(t.x) == t.m * p
                        if m == 1:
                            assert t == s
                            counts["terminal"] += 1
                        else:
                            assert t.m < m
                            branch = "even-halving" if m % 2 == 0 else "odd-centered"
                            counts[branch] += 1
                            if m % 2:
                                r = tuple(centered(a, m) for a in x)
                                assert all(abs(a) <= (m - 1) // 2 for a in r)
                                assert norm(r) % m == 0
                                z = mul(x, conj(r))
                                assert all(a % m == 0 for a in z)
                        count += 1
        by_prime[str(p)] = count
    return {"primes": primes, "states_by_prime": by_prime,
            "total_states": sum(by_prime.values()), "branches": counts,
            "scope": "All signed ordered tuples of norm m*p, 1<=m<p."}


def sieve(top: int) -> list[int]:
    flags = [True] * (top + 1)
    flags[0:2] = [False, False]
    for a in range(2, top + 1):
        if flags[a]:
            for b in range(a * a, top + 1, a):
                flags[b] = False
    return [n for n, flag in enumerate(flags) if flag]


def constructor_checks() -> dict:
    primes = sieve(1000)
    prime_set = set(primes)
    for p in range(1001):
        assert is_prime(p) == (p in prime_set)
    active_branches = {"even-halving": 0, "odd-centered": 0}
    maximum_active_steps = 0
    for p in primes:
        initial = seed(p)
        assert 1 <= initial.m < p
        assert norm(initial.x) == initial.m * p
        if p > 2:
            assert initial.m <= (p - 1) // 2
        rows = prime_trace(p)
        for row in rows[1:]:
            active_branches[row["branch"]] += 1
        maximum_active_steps = max(maximum_active_steps, len(rows) - 1)
        assert norm(prime_rep(p)) == p
        if p <= 257:
            assert prime_rep(p) == prime_rep(p, literal_clock=True)
    for n in range(1001):
        x = four_squares(n)
        assert all(0 <= a <= n for a in x)
        assert norm(x) == n
        if n <= 128:
            assert x == four_squares(n, literal_clock=True)
            assert norm(bounded_reference(n)) == n
    examples = []
    for n in [0, 1, 7, 23, 31, 65, 310, 2026, 1000000, 20261122]:
        x = four_squares(n)
        assert norm(x) == n
        examples.append({"n": n, "witness": x, "norm": norm(x)})
    return {"all_n_interval": [0, 1000], "all_n_count": 1001,
            "all_primes_at_most": 1000, "prime_count": len(primes),
            "prime_trace_branches": active_branches,
            "maximum_active_prime_steps": maximum_active_steps,
            "literal_clock_integer_interval": [0, 128],
            "literal_clock_prime_bound": 257,
            "independent_enumeration_interval": [0, 128], "examples": examples}


def main() -> None:
    dest = Path(__file__).resolve().parent.parent / "validation"
    dest.mkdir(exist_ok=True)
    result = {"status": "PASS", "python_version": sys.version.split()[0],
              "scope": "Symbolic and finite exact-arithmetic checks; not a formal proof.",
              "symbolic": symbolic_checks(),
              "descent": exhaustive_descent_states(),
              "construction": constructor_checks(),
              "lean_compiled": False,
              "ipra_object_derivation_completed": False}
    (dest / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    traces = {str(p): prime_trace(p) for p in [7, 23, 31, 79, 103, 199, 997]}
    (dest / "prime_traces.json").write_text(json.dumps(traces, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
