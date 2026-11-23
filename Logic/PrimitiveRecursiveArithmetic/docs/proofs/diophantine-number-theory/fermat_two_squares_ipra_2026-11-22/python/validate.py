"""Reproduce bounded validation, including independent finite comparisons.

This is testing of executable artifacts, not a substitute for the proof.
Run from this directory: python3 validate.py --limit 20000
"""
from __future__ import annotations

from dataclasses import asdict, replace
from pathlib import Path
import argparse
import json
import math
import platform
import time

from two_squares import (
    DescentState, collision_bounded, collision_table, descent_step,
    descent_trace, grid_from_root, half_factorial_mod, isqrt_pr, prime_bit,
    verify_descent, verify_grid, witness,
)


def sieve(limit: int) -> list[int]:
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for d in range(2, math.isqrt(limit) + 1):
        if flags[d]:
            flags[d * d:limit + 1:d] = b"\x00" * (((limit - d * d) // d) + 1)
    return [n for n in range(2, limit + 1) if flags[n]]


def represented_table(limit: int) -> list[bool]:
    """Independent enumeration of all possible a,b, not Wilson or a grid."""
    answer = [False] * (limit + 1)
    for a in range(math.isqrt(limit) + 1):
        for b in range(a, math.isqrt(limit - a * a) + 1):
            answer[a * a + b * b] = True
    return answer


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=20000)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1] / "validation")
    args = parser.parse_args()
    limit, out = args.limit, args.out
    if limit < 101:
        parser.error("use --limit at least 101")
    out.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    primes = sieve(limit)
    target = [p for p in primes if p % 4 == 1]
    independent = represented_table(limit)
    examples = []
    grid_count = descent_count = 0
    max_steps = (0, 0)
    for p in primes:
        assert independent[p] == (p == 2 or p % 4 == 1), p
        if p == 2:
            assert witness(p) == (1, 1)
        if p % 4 != 1:
            continue
        t = half_factorial_mod(p)
        assert (t * t + 1) % p == 0, p
        c = grid_from_root(p, t)
        assert verify_grid(c), (p, c)
        assert c.a > 0 and c.b > 0, p
        grid_count += 1
        trace = descent_trace(p, t)
        assert verify_descent(p, trace), (p, trace)
        descent_count += 1
        steps = len(trace) - 1
        if steps > max_steps[0]:
            max_steps = (steps, p)
        if p in (5, 13, 17, 29, 37, 41, 61, 97, 101, 1009, 10009, 19997):
            examples.append({"grid": asdict(c), "descent": [asdict(s) for s in trace]})
        # The certificate checker must detect a deliberately false output.
        assert not verify_grid(replace(c, a=c.a + 1))

    # Independent integer-square-root and primality checks, including 0 and 1.
    small_limit = min(limit, 1000)
    prime_set = set(primes)
    for n in range(small_limit + 1):
        assert isqrt_pr(n) == math.isqrt(n), n
        assert prime_bit(n) == (n in prime_set), n
    # Verify the finite modular-factorial recurrence against exact factorial.
    for p in primes:
        if p <= 500:
            assert half_factorial_mod(p) == math.factorial((p - 1) // 2) % p

    # Compare optimized lookup with the direct bounded-pair specification.
    collision_cases = 0
    for n in range(1, 81):
        side = math.isqrt(n) + 1
        for t in range(n):
            assert collision_table(n, t, side) == collision_bounded(n, t, side)
            collision_cases += 1

    # Test the stronger root-to-squares lemma for every residue and n <= 200.
    root_cases = 0
    for n in range(1, 201):
        for t in range(n):
            if (t * t + 1) % n == 0:
                assert verify_grid(grid_from_root(n, t)), (n, t)
                root_cases += 1

    # Check every bounded valid signed descent state for primes <= 101.
    # This exercises transitions outside the one chosen factorial orbit.
    state_cases = 0
    for p in sieve(101):
        for a in range(1 - p, p):
            for b in range(1 - p, p):
                norm = a * a + b * b
                if norm % p:
                    continue
                m = norm // p
                if 1 <= m < p:
                    old = DescentState(m, a, b)
                    new = descent_step(old)
                    assert new.a ** 2 + new.b ** 2 == p * new.m
                    if m == 1:
                        assert old == new
                    else:
                        assert 1 <= new.m < m and 2 * new.m <= m
                    state_cases += 1

    status = {
        "status": "PASS",
        "scope": "Finite executable validation; no claim of Lean compilation or object-iPRA checking.",
        "python": platform.python_version(),
        "limit": limit,
        "all_primes_checked_against_independent_sum_table": len(primes),
        "odd_target_primes_with_grid_certificates": grid_count,
        "odd_target_primes_with_descent_certificates": descent_count,
        "small_n_primality_and_isqrt_crosschecks": small_limit + 1,
        "table_vs_bounded_collision_cases": collision_cases,
        "general_modular_root_cases_through_200": root_cases,
        "valid_signed_descent_states_through_prime_101": state_cases,
        "max_active_descent_steps": max_steps[0],
        "first_prime_attaining_max_steps": max_steps[1],
        "elapsed_seconds": round(time.monotonic() - start, 3),
    }
    (out / "validation.json").write_text(json.dumps(status, indent=2) + "\n")
    (out / "examples.json").write_text(json.dumps(examples, indent=2) + "\n")
    lines = ["p,t,h,i,j,a,b,active_descent_steps"]
    for item in examples:
        c = item["grid"]
        values = [c[name] for name in ("n", "t", "h", "i", "j", "a", "b")]
        lines.append(",".join(map(str, values + [len(item["descent"]) - 1])))
    (out / "examples.csv").write_text("\n".join(lines) + "\n")
    print(json.dumps(status, indent=2))


if __name__ == "__main__":
    main()
