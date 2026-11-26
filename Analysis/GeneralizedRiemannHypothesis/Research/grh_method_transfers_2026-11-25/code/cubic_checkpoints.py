#!/usr/bin/env python3
"""Finite numerical illustration of the constant-free cubic criterion.

Field K=Q(alpha), alpha^3-alpha-1=0, discriminant -23.
Local splitting calculations use exact modular arithmetic. Sums use binary64
with compensated summation; they are illustrations, not interval certificates.
No finite run can verify the theorem's all-n quantifier.
"""
import argparse
import csv
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def primes_up_to(n):
    flags = bytearray(b"\x01") * (n + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if flags[p]:
            flags[p * p:n + 1:p] = b"\x00" * ((n - p * p) // p + 1)
    return (p for p in range(2, n + 1) if flags[p])


def mul_mod_f(a, b, p):
    # x^3=x+1 and x^4=x^2+x modulo x^3-x-1.
    t = [0] * 5
    for i in range(3):
        for j in range(3):
            t[i + j] += a[i] * b[j]
    return ((t[0] + t[3]) % p, (t[1] + t[3] + t[4]) % p,
            (t[2] + t[4]) % p)


def x_power_mod_f(n, p):
    a, b = (1, 0, 0), (0, 1, 0)
    while n:
        if n & 1:
            a = mul_mod_f(a, b, p)
        b = mul_mod_f(b, b, p)
        n >>= 1
    return a


def splitting(p):
    if p == 23:
        return "ramified", (1, 1)
    if p == 2:
        return "3", (3,)
    legendre = pow((-23) % p, (p - 1) // 2, p)
    if legendre == p - 1:
        return "12", (1, 2)
    assert legendre == 1
    if x_power_mod_f(p, p) == (0, 1, 0):
        return "111", (1, 1, 1)
    return "3", (3,)


class Compensated:
    def __init__(self):
        self.value = 0.0
        self.correction = 0.0

    def add(self, value):
        y = value - self.correction
        z = self.value + y
        self.correction = (z - self.value) - y
        self.value = z


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=20)
    args = ap.parse_args()
    N = args.max_n
    assert N >= 1
    limit = (2 * N) ** 4
    checkpoints = sorted({n ** 4 for n in range(1, N + 1)} |
                         {(2 * n) ** 4 for n in range(1, N + 1)})
    events, prime_events, small, counts = [], [], [], {"111": 0, "12": 0, "3": 0, "ramified": 0}
    for p in primes_up_to(limit):
        kind, degrees = splitting(p)
        counts[kind] += 1
        if p < 1000:
            roots = sum((x ** 3 - x - 1) % p == 0 for x in range(p))
            assert roots == sum(f == 1 for f in degrees)
            small.append({"p": p, "residue_degrees": degrees, "roots_mod_p": roots})
        pk, k, logp = p, 1, math.log(p)
        root_count = sum(f == 1 for f in degrees)
        if p != 23 and root_count:
            prime_events.append((p, root_count * logp))
        while pk <= limit:
            coefficient = sum(f for f in degrees if k % f == 0)
            if coefficient:
                events.append((pk, coefficient * logp))
            pk *= p
            k += 1
    (ROOT / "results").mkdir(exist_ok=True)
    output = {}
    for label, data, filename in [("prime_only", prime_events, "cubic_checkpoints.csv"),
                                  ("full_prime_powers", events, "cubic_primepower_checkpoints.csv")]:
        data.sort()
        S, total, divided = {}, Compensated(), Compensated()
        pos = 0
        for x in checkpoints:
            while pos < len(data) and data[pos][0] <= x:
                n, weight = data[pos]
                total.add(weight)
                divided.add(weight / n)
                pos += 1
            S[x] = divided.value - total.value / x
        result = []
        for n in range(1, N + 1):
            x, y = n ** 4, (2 * n) ** 4
            B = math.log(16) - (S[y] - S[x])
            result.append({"n": n, "x": x, "16x": y, "S_x": S[x], "S_16x": S[y],
                           "B_n": B, "n2_B_n": n * n * B})
        with (ROOT / "results" / filename).open("w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=list(result[0]))
            writer.writeheader()
            writer.writerows(result)
        output[label] = {"events": len(data),
                         "max_scaled_checkpoint": max(r["n2_B_n"] for r in result),
                         "min_scaled_checkpoint": min(r["n2_B_n"] for r in result)}
    meta = {"field_polynomial": "x^3-x-1", "discriminant": -23, "max_n": N,
            "max_prime_power": limit, "splitting_counts": counts,
            "small_prime_checks": len(small), "finite_weight_events": len(events),
            "arithmetic": "modular splitting exact; compensated binary64 sums",
            "claim": "finite illustration only; does not verify an asymptotic upper bound",
            "statistics": output}
    (ROOT / "results/cubic_summary.json").write_text(json.dumps(meta, indent=2) + "\n")
    (ROOT / "results/cubic_small_primes.json").write_text(json.dumps(small, indent=2) + "\n")
    print(json.dumps(meta, indent=2))


if __name__ == "__main__":
    main()
