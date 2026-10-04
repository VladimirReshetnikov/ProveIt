#!/usr/bin/env python3
"""Fresh standard-library-only checks; no prior/upstream program is executed."""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from math import gcd
from pathlib import Path
import json


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "native-gap-halting-continuation-20261004" / "PROOF.md"
SOURCE_HASH = "8cc5911e528d0555ee89fe63f0e30b8a3eac4a32e3e4237ee9b00a38107a7d1b"
RHO = Fraction(743, 1125)
ALPHA = [Fraction(34, 15), Fraction(61, 30), Fraction(31, 15), Fraction(32, 15)]
BETA = [Fraction(1261, 225), Fraction(2329, 450), Fraction(1189, 225), Fraction(1223, 225)]


def primitive(a, b):
    """Derive the primitive triple directly, without using its classified gcd."""
    m = max(a, b)
    total = 20 * 2**m
    u = 2**m + 2 ** (m - a + 1)
    w = 2**m + 2 ** (m - b + 1)
    v = total - u - w
    common = gcd(gcd(u, v), w)
    triple = (u // common, v // common, w // common)
    d = sum(triple)
    assert d >= 2 ** (m + 1)
    assert gcd(gcd(triple[0], triple[1]), triple[2]) == 1
    assert Fraction(triple[0], d) == Fraction(1, 20) + Fraction(1, 10 * 2**a)
    assert Fraction(triple[2], d) == Fraction(1, 20) + Fraction(1, 10 * 2**b)
    return d, triple


def f(b, n):
    out = 0
    k = 0
    while n:
        out += (2 * k + 1) * n
        n //= b
        k += 1
    return out


def digital_f(b, n):
    original = n
    s = w = k = 0
    while n:
        n, d = divmod(n, b)
        s += d
        w += k * d
        k += 1
    return Fraction(b * (b + 1) * original - (3 * b - 1) * s, (b - 1) ** 2) - Fraction(2 * w, b - 1)


def count_formula(n):
    return f(2, n // 10) + f(16, n // 16) - f(16, n // 80)


def v2(n):
    assert n > 0
    return (n & -n).bit_length() - 1


def shell_formula(n):
    v = v2(n)
    return v * v if n % 5 == 0 else (v // 4) ** 2


def direct_count(n):
    # The proved lower bound makes this a safe finite superset of all contributors.
    bound = n.bit_length()
    return sum(n // primitive(a, b)[0] for a in range(bound + 1) for b in range(bound + 1))


def main():
    assert sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_HASH
    ceiling = 200000
    bound = ceiling.bit_length()
    primitive_scales = Counter()
    primitive_shapes = set()
    for a in range(bound + 1):
        for b in range(bound + 1):
            d, triple = primitive(a, b)
            assert triple not in primitive_shapes
            primitive_shapes.add(triple)
            if d <= ceiling:
                primitive_scales[d] += 1
    shells = [0] * (ceiling + 1)
    for d, multiplicity in primitive_scales.items():
        for n in range(d, ceiling + 1, d):
            shells[n] += multiplicity
    cumulative = distinct = 0
    inverse_ranks = 0
    for n in range(1, ceiling + 1):
        assert shells[n] == shell_formula(n), n
        cumulative += shells[n]
        distinct += int(shells[n] > 0)
        assert cumulative == count_formula(n), n
        assert distinct == n // 10 + n // 16 - n // 80, n
        error = RHO * n - cumulative
        ell = n.bit_length() - 1
        assert 0 <= error < ell * ell + 4 * ell + 6, n
        # All ranks in a nonempty shell have inverse total n, by the prefix count.
        if shells[n]:
            first = cumulative - shells[n] + 1
            last = cumulative
            assert Fraction(first, RHO) <= n
            assert Fraction(last, RHO) <= n
            inverse_ranks += shells[n]
    digital_checks = 0
    for b in range(2, 21):
        for n in range(5001):
            assert f(b, n) == digital_f(b, n), (b, n)
            digital_checks += 1
    for m in range(1, 301):
        n = 10 * 2**m
        a = count_formula(n)
        previous = count_formula(n - 1)
        e = RHO * n - a
        assert e == ALPHA[m % 4] * m + BETA[m % 4], m
        assert a - previous == (m + 1) ** 2, m
        assert RHO * (n - 1) - previous == e + (m + 1) ** 2 - RHO, m
        first = previous + 1
        assert Fraction(n) - Fraction(first, RHO) == (e + (m + 1) ** 2 - 1) / RHO
        assert Fraction(n) - Fraction(a, RHO) == e / RHO
        if m <= 32:
            assert a == direct_count(n), m
            assert previous == direct_count(n - 1), m
    exact_rho = Fraction(1, 10) * Fraction(1 + Fraction(1, 2), (1 - Fraction(1, 2)) ** 2) + (Fraction(1, 16) - Fraction(1, 80)) * Fraction(1 + Fraction(1, 16), (1 - Fraction(1, 16)) ** 2)
    assert exact_rho == RHO
    assert sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_HASH
    result = {
        "status": "all checks passed",
        "source_sha256_before_and_after": SOURCE_HASH,
        "scope": "All encoded triples, independent of halting; finite checks supplement the written proof.",
        "rho": str(RHO),
        "distinct_scale_density": "3/20",
        "exhaustive_total_range": [1, ceiling],
        "gcd_derived_counter_square": [0, bound],
        "digital_identity_bases": [2, 20],
        "digital_identity_argument_range": [0, 5000],
        "digital_identity_checks": digital_checks,
        "exact_subsequence_M_range": [1, 300],
        "gcd_direct_subsequence_M_range": [1, 32],
        "inverse_ranks_covered_by_checked_shell_blocks": inverse_ranks,
        "A_at_ceiling": cumulative,
        "B_at_ceiling": distinct,
        "samples": [{"N": n, "A": count_formula(n), "J": shell_formula(n), "E": str(RHO * n - count_formula(n))} for n in [10, 16, 20, 40, 80, 160, 256, 1000, ceiling]],
    }
    (ROOT / "checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
