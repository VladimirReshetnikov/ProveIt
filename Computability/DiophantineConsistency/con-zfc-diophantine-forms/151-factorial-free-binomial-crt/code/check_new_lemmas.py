#!/usr/bin/env python3
"""Finite regressions for the new unbounded lemmas (not a proof of Con(ZFC)).

Only the Python standard library is used. Required checks are explicit;
running Python with -O does not remove them. No root search is attempted.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import random
from collections import Counter
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def factor(n):
    require(n >= 1, "factor input must be positive")
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def vp(n, p):
    require(n > 0, "valuation input must be positive")
    v = 0
    while n % p == 0:
        v += 1
        n //= p
    return v


def binomial_factors(R, t):
    interval = [factor(R + i) for i in range(1, t + 1)]
    exponents = Counter()
    for f in interval:
        exponents.update(f)
    exponents.subtract(factor(math.factorial(t)))
    require(all(e >= 0 for e in exponents.values()), "negative binomial valuation")
    exponents = {p: e for p, e in exponents.items() if e}
    B = math.comb(R + t, t)
    require(math.prod(p ** e for p, e in exponents.items()) == B,
            "interval valuation does not reconstruct binomial")
    return B, exponents, interval


def check_coverage(R, t):
    B, exponents, interval = binomial_factors(R, t)
    L = math.lcm(*range(1, t + 1))
    require(R >= L * L, "test is outside the stated uniform threshold")
    for p, e in exponents.items():
        maximum = max(f.get(p, 0) for f in interval)
        require(e <= maximum, "all-prime completeness failed")
        require(any((R + i) % (p ** e) == 0 for i in range(1, t + 1)),
                "prime power has no compatible row")
    for i, f in enumerate(interval, 1):
        candidates = [p for p, v in f.items() if v > 2 * vp(L, p)]
        require(candidates, "row lacks high prime-power divisor")
        for p in candidates:
            v = f[p]
            d = vp(t * math.comb(t - 1, i - 1), p)
            require(d <= vp(L, p), "row denominator does not divide lcm")
            e = exponents.get(p, 0)
            require(e == v - d, "isolated prime valuation formula failed")
            require(p ** e > t and (R + i) % (p ** e) == 0,
                    "row isolating power failed")
    return len(exponents)


def crt(residues, moduli):
    M = math.prod(moduli)
    value = sum(a * (M // m) * pow(M // m, -1, m)
                for a, m in zip(residues, moduli)) % M
    return value if value else M


def local_polynomial(i, w, wanted):
    return math.prod((i - j) ** 2 + (w - a) ** 2
                     for j, a in enumerate(wanted))


def crt_fixture(t, R, seed):
    B, exponents, interval = binomial_factors(R, t)
    rng = random.Random(seed)
    wanted = [rng.randrange(t) for _ in range(t)]
    # On the bounded box every factor is at most 2(t-1)^2.
    bound = max(1, (2 * max(1, t - 1) ** 2) ** t)
    K = max(t, bound.bit_length() + 1)
    N = B ** K
    moduli, cres, ares = [], [], []
    for p, e in sorted(exponents.items()):
        chosen = max(range(t), key=lambda j: interval[j].get(p, 0))
        moduli.append(p ** (2 * K * e))
        cres.append(chosen)
        ares.append(wanted[chosen])
    C, A = crt(cres, moduli), crt(ares, moduli)
    require(1 <= C <= N * N and 1 <= A <= N * N, "CRT representative bound")
    require((C + R + 1) % B == 0, "raw index congruence")
    require(math.comb(C, t) % N == 0, "index range")
    require(math.comb(A, t) % N == 0, "column range")
    require(local_polynomial(C, A, wanted) % N == 0, "local congruence")
    for row in range(t):
        choices = [(p, e) for p, e in exponents.items()
                   if p ** e > t and (R + row + 1) % (p ** e) == 0]
        require(choices, "missing row selector")
        for p, e in choices:
            modulus = p ** (K * e)
            i, w = C % modulus, A % modulus
            require(i == row and 0 <= w < t, "bounded residue decoding")
            require(local_polynomial(i, w, wanted) == 0, "decoded false row")
    return {"t": t, "R": R, "K": K, "prime_count": len(exponents),
            "N_bits": N.bit_length()}


def multiply_linear(coefficients, j):
    out = [0] * (len(coefficients) + 1)
    for k, c in enumerate(coefficients):
        out[k] += c
        out[k + 1] += j * c
    return out


def run():
    counts = Counter()
    digest = hashlib.sha256()
    for t in range(1, 13):
        L = math.lcm(*range(1, t + 1))
        for i in range(1, t + 1):
            D = t * math.comb(t - 1, i - 1)
            require(L % D == 0, "classical binomial-lcm divisibility")
            counts["binomial_lcm_cases"] += 1
        for offset in range(24):
            R = L * L + offset
            counts["prime_packets"] += check_coverage(R, t)
            counts["coverage_cases"] += 1
            digest.update(f"{t},{R};".encode())
    fixtures = []
    for t in range(2, 7):
        L = math.lcm(*range(1, t + 1))
        for off in (0, 1, 7):
            fixtures.append(crt_fixture(t, L * L + off, 101 * t + off))
    counts["constructive_crt_fixtures"] = len(fixtures)

    for p in (2, 3, 5, 7):
        for e in range(1, 5):
            pe = p ** e
            for a in range(121):
                for k in range(1, 16):
                    value = math.comb(a, k) if a >= k else 0
                    if value % pe == 0:
                        require(a % pe < k, "one-sided binomial range lemma")
                    counts["range_cases"] += 1

    for t in range(1, 7):
        F = (2 * (t + 1)) ** t
        seen = {}
        for length in range(2 * t + 2):
            for labels in itertools.combinations_with_replacement(range(1, t + 1), length):
                coeff = [1]
                for j in labels:
                    coeff = multiply_linear(coeff, j)
                value = math.prod(1 + j * F for j in labels)
                if length <= t:
                    require(sum(coeff) < F, "equal-degree label coefficient majorant")
                    if value in seen:
                        require(seen[value] == labels, "label collision at prescribed base")
                    seen[value] = labels
                else:
                    require(value not in seen, "unequal factor-count collision")
                counts["label_multisets"] += 1

    for t in range(1, 49):
        F = (2 * (t + 1)) ** t
        R = F * F
        B = math.comb(R + t, t)
        require(B % 2 == 1, "odd binomial completeness")
        require(F > math.factorial(t), "explicit power does not dominate factorial")
        odd_part = math.factorial(t)
        while odd_part % 2 == 0:
            odd_part //= 2
        for h in (1, 3, 7):
            v = odd_part * h
            y = F * v * v
            require(y % math.factorial(t) == 0 and y % 2 == 0,
                    "cofinal square beta base")
            counts["cofinal_beta_cases"] += 1
        counts["parity_cases"] += 1

    # Without a size/coverage hypothesis the global certificate is false.
    t, R, B, K, C = 2, 1, 3, 2, 1
    N = B ** K
    require(B == math.comb(R + t, t), "negative control binomial")
    require((C + R + 1) % B == 0 and math.comb(C, t) % N == 0,
            "negative control congruences")
    require((C - 1) ** 2 % N == 0 and (0 - 1) ** 2 != 0,
            "negative control must conceal a false row")
    counts["explicit_missing_hypothesis_counterexamples"] = 1
    return {"status": "passed", "scope": "finite regression checks; unbounded proofs are in report",
            "counts": dict(sorted(counts.items())), "fixtures": fixtures,
            "coverage_digest": digest.hexdigest(),
            "counterexample": {"t": t, "R": R, "B": B, "K": K, "C": C,
                               "local_polynomial": "(i-1)^2", "false_row": 0}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    result = run()
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(payload)
    print(payload)


if __name__ == "__main__":
    main()
