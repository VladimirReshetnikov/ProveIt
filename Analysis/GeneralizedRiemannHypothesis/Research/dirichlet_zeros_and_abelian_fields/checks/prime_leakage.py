#!/usr/bin/env python3
"""Finite arithmetic side of the smooth logarithmic prime packets.

With no arguments, print the JSON table. Run with --check PATH to compare
a saved table, allowing small differences between floating-point libraries.
Only the Python standard library is required.
"""

import argparse
from bisect import bisect_left, bisect_right
import cmath
import json
import math
from pathlib import Path
from statistics import mean, median


SCALES = (100, 1000, 3000)
BANDWIDTH_FACTORS = (1, 4, 12)


def prime_powers(limit):
    """Return the primes, and sorted pairs (prime power n, log of its base)."""
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p :: p] = bytes((limit - p * p) // p + 1)
    primes = [n for n in range(2, limit + 1) if sieve[n]]
    powers = []
    for p in primes:
        n = p
        while n <= limit:
            powers.append((n, math.log(p)))
            n *= p
    return primes, sorted(powers)


def outside_terms(p, powers, indices):
    """Unmodulated, off-center nonzero contributions in the compact support."""
    left = bisect_left(indices, p * math.exp(-0.5))
    right = bisect_right(indices, p * math.exp(0.5))
    log_p = math.log(p)
    terms = []
    for n, von_mangoldt in powers[left:right]:
        if n == p:
            continue
        u = math.log1p((n - p) / p)
        if abs(u) < 0.5:
            window = (1 - 4 * u * u) ** 4
            terms.append((n, u, window * von_mangoldt / log_p * math.sqrt(p / n)))
    return terms


def weighted_terms(terms, bandwidth):
    for n, u, weight in terms:
        v = bandwidth * u
        yield n, weight * (math.sin(v) / v) ** 2


def chi5(n):
    """Quartic primitive character modulo 5 normalized by chi(2)=i."""
    return (0j, 1 + 0j, 1j, -1j, -1 + 0j)[n % 5]


def rect(z):
    return [round(z.real, 10), round(z.imag, 10)]


def direct_packet(p, bandwidth, limit):
    """Slow independent check using trial division and summing every integer."""
    real_terms = []
    imag_terms = []
    off_center = []
    for n in range(2, limit + 1):
        u = math.log(n / p)
        if abs(u) >= 0.5:
            continue
        base = next((k for k in range(2, math.isqrt(n) + 1) if n % k == 0), n)
        m = n
        while m % base == 0:
            m //= base
        if m != 1:
            continue
        v = bandwidth * u
        sinc = math.sin(v) / v if v else 1.0
        weight = ((1 - 4 * u**2) ** 4 * sinc**2
                  * math.log(base) / math.log(p) * math.sqrt(p / n))
        z = chi5(n) * weight
        real_terms.append(z.real)
        imag_terms.append(z.imag)
        if n != p:
            off_center.append(weight)
    return complex(math.fsum(real_terms), math.fsum(imag_terms)), math.fsum(off_center)


def compute():
    limit = math.ceil(2 * max(SCALES) * math.exp(0.5))
    primes, powers = prime_powers(limit)
    indices = [n for n, _ in powers]
    rows = []
    example = None
    for x in SCALES:
        band_primes = [p for p in primes if x <= p <= 2 * x]
        terms = {p: outside_terms(p, powers, indices) for p in band_primes}
        for factor in BANDWIDTH_FACTORS:
            bandwidth = factor * x / math.log(x)
            leakages = {
                p: math.fsum(weight for _, weight in weighted_terms(terms[p], bandwidth))
                for p in band_primes
            }
            values = list(leakages.values())
            rows.append({
                "X": x, "D": factor, "B": round(bandwidth, 10),
                "primes_in_band": len(values),
                "mean_leakage": round(mean(values), 10),
                "median_leakage": round(median(values), 10),
                "maximum_leakage": round(max(values), 10),
                "number_with_leakage_at_most_one_quarter": sum(v <= 0.25 for v in values),
            })
            if x != 1000 or factor != 4:
                continue
            # Include a reproducible interior example, selected using only W and chi(p).
            p = next(p for p in band_primes if p >= 1.5 * x and
                     chi5(p).imag != 0 and leakages[p] <= 0.25)
            weighted = list(weighted_terms(terms[p], bandwidth))
            full = chi5(p) + complex(
                math.fsum(chi5(n).real * w for n, w in weighted),
                math.fsum(chi5(n).imag * w for n, w in weighted),
            )
            conjugate = chi5(p).conjugate() + sum(
                (chi5(n).conjugate() * w for n, w in weighted), 0j)
            direct_full, direct_leakage = direct_packet(p, bandwidth, limit)
            assert cmath.isclose(full, direct_full, rel_tol=1e-10)
            assert math.isclose(leakages[p], direct_leakage, abs_tol=1e-11)
            assert abs(full - chi5(p)) <= leakages[p] + 1e-12
            assert cmath.isclose(conjugate, full.conjugate(), abs_tol=1e-12)
            example = {
                "X": x, "D": factor, "prime": p, "off_center_prime_powers": len(weighted),
                "selection": "first prime p >= 3X/2 with imaginary chi(p) and W_p <= 1/4",
                "chi_main_re_im": rect(chi5(p)), "chi_full_re_im": rect(full),
                "conjugate_chi_main_re_im": rect(chi5(p).conjugate()),
                "conjugate_chi_full_re_im": rect(conjugate),
                "single_character_error": round(abs(full - chi5(p)), 10),
                "leakage": round(leakages[p], 10),
                "full_packet_separation": round(abs(full - conjugate), 10),
            }
    return {
        "normalization": "p in [X,2X]; u=log(n/p); B=D*X/log(X); sinc(v)=sin(v)/v",
        "weight": "Lambda(n)/log(p) * sqrt(p/n) * max(1-4*u^2,0)^4 * sinc(B*u)^2",
        "leakage": "sum of weights over prime powers n distinct from p",
        "arithmetic_packet": "sum of weights times chi(n) over all prime powers including p",
        "rows": rows,
        "quartic_character_mod_5": example,
    }


def matches(a, b):
    if isinstance(a, dict) and isinstance(b, dict):
        return a.keys() == b.keys() and all(matches(a[k], b[k]) for k in a)
    if isinstance(a, list) and isinstance(b, list):
        return len(a) == len(b) and all(matches(x, y) for x, y in zip(a, b))
    if isinstance(a, float) and isinstance(b, (int, float)):
        return math.isclose(a, b, rel_tol=1e-10, abs_tol=1e-9)
    return a == b


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path, metavar="PATH")
    args = parser.parse_args()
    result = compute()
    if args.check:
        if not matches(result, json.loads(args.check.read_text(encoding="utf-8"))):
            raise SystemExit("Recorded and recomputed tables differ.")
        print("All nine rows and the quartic-character example agree.")
    else:
        print(json.dumps(result, indent=2, ensure_ascii=False))
