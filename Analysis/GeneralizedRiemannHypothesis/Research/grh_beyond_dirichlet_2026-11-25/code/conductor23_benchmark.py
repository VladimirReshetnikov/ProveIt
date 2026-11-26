#!/usr/bin/env python3
"""Exact benchmark for the conductor-23 dihedral target.

Compare coefficients of eta(z)*eta(23*z) with the Euler product determined by
the splitting of x^3-x^2+1 modulo primes. Uses integer arithmetic only.
This checks finite coefficient identities and conventions; it proves no
statement about zeros of the associated L-function.
"""

import argparse
import csv
import json
from pathlib import Path


def primes_up_to(n):
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = b"\x00" * ((n - p * p) // p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def eta_coefficients(n):
    # q * product_{j>=1}(1-q^j)(1-q^(23j)), truncated through q^n.
    a = [0] * (n + 1)
    a[1] = 1
    for step in range(1, n):
        for j in range(n, step, -1):
            a[j] -= a[j - step]
    for step in range(23, n, 23):
        for j in range(n, step, -1):
            a[j] -= a[j - step]
    return a


def prime_data(p):
    if p == 23:
        roots = sum((x * x * x - x * x + 1) % p == 0 for x in range(p))
        assert roots == 2
        # Modulo 23 the polynomial is (x-15)(x-16)^2. Thus the cubic
        # zeta factor is (1-t)^(-2); dividing by the rational zeta factor
        # gives the standard Artin factor (1-t)^(-1).
        for x in range(p):
            assert (x * x * x - x * x + 1 - (x - 15) * (x - 16)**2) % p == 0
        return {"prime": p, "splitting_type": "ramified", "roots": roots,
                "a_p": 1, "quadratic_character": 0,
                "principal_selector_period": 1,
                "principal_selector_weight_log_p": 1}
    roots = sum((x * x * x - x * x + 1) % p == 0 for x in range(p))
    if roots not in (0, 1, 3):
        raise AssertionError((p, roots))
    # The Frobenius sign is +1 on identity and 3-cycles; -1 on transpositions.
    sign = -1 if roots == 1 else 1
    period = {3: 1, 1: 2, 0: 3}[roots]
    return {"prime": p, "splitting_type": {3: "identity", 1: "transposition",
            0: "3-cycle"}[roots], "roots": roots, "a_p": roots - 1,
            "quadratic_character": sign,
            "principal_selector_period": period,
            "principal_selector_weight_log_p": 2}


def euler_coefficients(n, rows):
    a = [0] * (n + 1)
    a[1] = 1
    for row in rows:
        p, ap, sign = row["prime"], row["a_p"], row["quadratic_character"]
        powers = [(1, 1)]
        q, prev, curr = p, 1, ap
        while q <= n:
            powers.append((q, curr))
            q, prev, curr = q * p, curr, ap * curr - sign * prev
        # Each integer gets its p-adic component exactly once.
        old = a[:]
        for q, coefficient in powers[1:]:
            for m in range(1, n // q + 1):
                if m % p:
                    a[q * m] = old[m] * coefficient
    return a


def check_selector(rows):
    # Verify the class-character logarithmic-derivative formula on powers.
    checked = 0
    for row in rows:
        for k in range(1, 13):
            p = row["prime"]
            if p == 23:
                zeta_k, l_theta = 1, 1
            elif row["splitting_type"] == "identity":
                zeta_k, l_theta = 2, 2
            elif row["splitting_type"] == "transposition":
                zeta_k = 2 if k % 2 == 0 else 0
                l_theta = zeta_k
            else:
                zeta_k, l_theta = 2, 2 if k % 3 == 0 else -1
            numerator = zeta_k + 2 * l_theta
            expected = row["principal_selector_weight_log_p"] if (
                k % row["principal_selector_period"] == 0) else 0
            assert numerator == 3 * expected, (p, k, numerator, expected)
            checked += 1
    return checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=2000)
    parser.add_argument("--output", type=Path, default=Path("conductor23-results"))
    args = parser.parse_args()
    if not 23 <= args.limit <= 20000:
        parser.error("limit must be between 23 and 20000")
    rows = [prime_data(p) for p in primes_up_to(args.limit)]
    a_eta = eta_coefficients(args.limit)
    a_euler = euler_coefficients(args.limit, rows)
    mismatches = [n for n in range(1, args.limit + 1) if a_eta[n] != a_euler[n]]
    assert not mismatches, mismatches[:10]
    selector_checks = check_selector(rows)
    args.output.mkdir(parents=True, exist_ok=True)
    with (args.output / "prime_coefficients.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    summary = {"target": "eta(z) eta(23 z)", "coefficient_limit": args.limit,
        "primes_checked": len(rows), "eta_euler_mismatches": mismatches,
        "selector_prime_power_checks": selector_checks,
        "all_checks_passed": True,
        "first_coefficients": {str(n): a_eta[n] for n in range(1, 31)},
        "scope": "Exact finite coefficient checks only; no L-function zero theorem."}
    (args.output / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
