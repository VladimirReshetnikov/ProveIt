"""Independent checks of finite identities and approximation implementations.

No check claims to verify the PNT, a zero-free strip, or iPRA provability.
mpmath is used only as an independent high-precision numerical comparator.
"""
from fractions import Fraction
from pathlib import Path
import json
import random
import mpmath as mp

from arithmetic import (finite_abel, log_interval, li_interval, prime_count,
                        cleared_matrix, bit_length, threshold_exponent)

mp.mp.dps = 100


def real(q: Fraction):
    return mp.mpf(q.numerator) / q.denominator


def run():
    checks = {}
    rng = random.Random(20261115)
    for length in range(50):
        a = [Fraction(rng.randint(-30, 30), rng.randint(1, 17)) for _ in range(length)]
        b = [Fraction(rng.randint(-30, 30), rng.randint(1, 17)) for _ in range(length)]
        lhs, rhs = finite_abel(a, b)
        assert lhs == rhs
    checks["exact_signed_rational_abel_cases"] = 50

    count = 0
    for u in (Fraction(1), Fraction(3, 2), Fraction(2), Fraction(17, 3),
              Fraction(100), Fraction(1000000)):
        for v in (0, 1, 4, 12, 24):
            lo, hi = log_interval(u, v)
            target = mp.log(real(u))
            assert real(lo) <= target <= real(hi)
            assert hi - lo <= Fraction(1, 1 << v)
            count += 1
    checks["log_enclosures_compared_to_100_digit_mpmath"] = count

    samples = []
    for n, v in ((2, 0), (3, 0), (3, 2), (5, 1), (8, 1)):
        lo, hi = li_interval(n, v)
        target = mp.li(n) - mp.li(2)
        assert real(lo) <= target <= real(hi)
        samples.append({"n": n, "precision": v,
                        "interval_low": mp.nstr(real(lo), 18),
                        "interval_high": mp.nstr(real(hi), 18),
                        "reference": mp.nstr(target, 18)})
    checks["Li_enclosures_compared_to_100_digit_mpmath"] = samples

    count = 0
    for n in range(2, 31):
        for m in range(3):
            for v in range(3):
                q = Fraction(rng.randint(0, 100), rng.randint(1, 19))
                rhs = Fraction(n, (1 << m) * bit_length(n)) + Fraction(1, 1 << v)
                rational = abs(prime_count(n) - q) <= rhs
                assert cleared_matrix(n, m, v, q) == rational
                count += 1
    checks["cleared_denominator_equivalence_cases"] = count

    for k in (8192, 8193, 8200, 9000, 16384, 32768):
        assert (1 << 100) * k**9 <= (1 << (k // 8))
        assert 54 * (1 << 222) * k**20 <= (1 << (k // 4))
    checks["sample_dyadic_prefactor_inequalities"] = 12
    checks["prime_counts"] = {str(n): prime_count(n) for n in (10, 100, 1000)}
    assert checks["prime_counts"] == {"10": 4, "100": 25, "1000": 168}
    checks["threshold_exponent_at_m_0"] = str(threshold_exponent(0))
    checks["excluded_claims"] = ["No universal PNT test", "No zero-free-region computation",
                                 "No Lean compilation", "No iPRA proof checker run"]
    return checks


if __name__ == "__main__":
    result = run()
    output = Path(__file__).resolve().parents[1] / "verification.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
