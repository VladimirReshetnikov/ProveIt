#!/usr/bin/env python3
"""Meaningful finite checks; these do not replace the general proofs."""

import json
from fractions import Fraction as Q
from math import gcd, isqrt
from pathlib import Path

from arithmetic import (
    below_power, fundamental_pell, liouville_K, no_rational_root_certificate,
    pell_bound, pell_power, poly_eval, prime_factors, quadratic_example,
    root_interval, roth_certificate, sqrt2_roth_good, stormer_neighbors,
    supported,
)


def independent_smooth_set(S, limit):
    """Multiplicative generation, independent of the Pell algorithm."""
    values = {1}
    for p in S:
        old = list(values)
        for n in old:
            t = n
            for _ in range(limit.bit_length()):
                if t > limit:
                    break
                values.add(t)
                t *= p
    return values


def text_q(value):
    if isinstance(value, Q):
        return str(value)
    raise TypeError(type(value).__name__)


def main():
    out = Path(__file__).resolve().parent.parent / "verification"
    out.mkdir(exist_ok=True)
    checks = []

    for base in range(2, 12):
        for exponent in range(9):
            for n in (0, 1, max(0, base ** exponent - 1), base ** exponent,
                      base ** exponent + 1, 173):
                assert below_power(n, base, exponent) == (n < base ** exponent)
    checks.append("Compressed power comparison: boundary cases and selected inputs for bases 2..11, exponents 0..8 PASS")

    pell_count = 0
    for D in range(2, 51):
        if isqrt(D) ** 2 == D:
            assert fundamental_pell(D) is None
            continue
        u, v = fundamental_pell(D)
        assert u * u - D * v * v == 1
        base, exponent = pell_bound(D)
        assert below_power(u, base, exponent) and below_power(v, base, exponent)
        for m in range(1, 11):
            x, y = pell_power(D, u, v, m)
            assert x * x - D * y * y == 1
            if supported(y, prime_factors(D)):
                assert m == 1
        pell_count += 1
    checks.append(f"Pell identities and smooth-coordinate lemma: {pell_count} nonsquare D, ten powers each PASS")

    tables = {}
    for S in ((), (3, 5), (2,), (2, 3), (2, 3, 5)):
        ns, table = stormer_neighbors(S)
        smooth = independent_smooth_set(S, 100000)
        brute = sorted(n for n in smooth if n + 1 in smooth)
        assert ns == brute
        assert len(ns) <= 3 ** len(S) - 2 ** len(S)
        tables[",".join(map(str, S))] = {"neighbors": [[n, n + 1] for n in ns],
                                         "pell_candidates": table}
    expected = [1, 2, 3, 4, 5, 8, 9, 15, 24, 80]
    assert stormer_neighbors((2, 3, 5))[0] == expected
    (out / "stormer_examples.json").write_text(json.dumps(tables, indent=2) + "\n")
    checks.append("Størmer enumeration: five prime sets agree with independent smooth generation through 100000 PASS")

    coeffs, R = [-2, 0, 1], 2
    assert no_rational_root_certificate(coeffs)
    assert not no_rational_root_certificate([-1, 0, 1])
    K = liouville_K(coeffs, R)
    assert K == 6
    for k in range(12):
        lo, hi = root_interval(coeffs, 1, 2, 2 * R + k)
        assert 0 < hi - lo <= Q(1, 2 ** k)
        assert abs(poly_eval(coeffs, lo)) <= K * Q(1, 2 ** k)
        for q in range(1, 18):
            for p in range(-4 * q, 4 * q + 1):
                assert abs(Q(p, q) - lo) + Q(1, 2 ** k) >= Q(1, K * q * q)
    checks.append("Root bisection and finite Liouville separation: exact rational grid PASS")

    good = []
    cutoff = K ** 2
    for q in range(1, 2 * cutoff + 1):
        for p in range(0, 3 * q + 1):
            if gcd(p, q) == 1 and sqrt2_roth_good(p, q):
                assert q < cutoff
                assert roth_certificate(coeffs, R, p, q, 1, 2, 80)
                good.append([p, q])
    (out / "quadratic_roth_example.json").write_text(json.dumps({
        "polynomial_low_to_high": coeffs, "epsilon": "1/2", "K": K,
        "proved_denominator_cutoff_exclusive": cutoff,
        "independent_exact_surd_scan_through": 2 * cutoff,
        "reduced_good_fractions": good,
    }, indent=2) + "\n")
    checks.append(f"Quadratic Roth: exact surd decision through q={2 * cutoff}, {len(good)} reduced exceptions, all q<{cutoff} PASS")

    examples = []
    for H in (8, 16, 32, 64):
        e = quadratic_example(H)
        c, b, a = e["coefficients"]
        al, ah = e["alpha_interval"]
        xl, xh = e["xi_interval"]
        assert poly_eval([c, b, a], al) * poly_eval([c, b, a], ah) < 0
        assert poly_eval([-2, 0, 0, 1], xl) < 0 < poly_eval([-2, 0, 0, 1], xh)
        disc = b * b - 4 * a * c
        assert disc > 0 and isqrt(disc) ** 2 != disc
        assert gcd(gcd(a, b), c) == 1
        assert max(abs(c), abs(b), abs(a)) == e["height"]
        assert e["scaled_error_upper"] < 16384
        examples.append(e)
    (out / "davenport_schmidt_examples.json").write_text(json.dumps(
        {"target": "real cube root of 2", "examples": examples,
         "status": "finite certificate examples only; the report proves the bounded construction under its stated primitive recursive name and separation-modulus hypotheses"},
        default=text_q, indent=2) + "\n")
    checks.append("Davenport–Schmidt illustrations: four primitive irreducible quadratic root certificates PASS")

    checks.append("No Lean compilation or object-iPRA derivation was executed.")
    checks.append("Finite computation supports the implementations; it does not prove the general theorems.")
    report = "\n".join(checks) + "\n"
    (out / "python_verification.txt").write_text(report)
    print(report)


if __name__ == "__main__":
    main()
