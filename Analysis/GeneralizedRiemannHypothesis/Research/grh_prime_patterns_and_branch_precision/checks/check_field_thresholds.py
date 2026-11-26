"""Certify the least dimensions for two-deletion edits over degree-n fields."""
from collections import Counter
from fractions import Fraction
from math import isqrt

SCALE = 10**12


def primes_below(bound):
    sieve = bytearray([1]) * bound
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(bound - 1) + 1):
        if sieve[p]:
            sieve[p*p:bound:p] = bytes(len(range(p*p, bound, p)))
    return [p for p, present in enumerate(sieve) if present]


def exceeds_threshold(lower, count, counts):
    # The scaled sum lies in [lower, lower+count).
    if 2 * lower > 11 * SCALE:
        return True
    if 2 * (lower + count) <= 11 * SCALE:
        return False
    return sum(Fraction(n, p) for p, n in counts.items()) > Fraction(11, 2)


def minimum_dimension(degree, primes):
    lower = count = 0
    counts = Counter()
    for p in primes:
        for _ in range(degree):
            lower += SCALE // p
            count += 1
            counts[p] += 1
            if exceeds_threshold(lower, count, counts):
                return count, p
    raise ValueError("Prime list too short")


if __name__ == "__main__":
    primes = primes_below(170000)
    for degree in range(2, 13):
        count, last = minimum_dimension(degree, primes)
        print(f"degree {degree:2}    coordinates {count:5}    last prime {last}")
    assert 431 in primes
    assert pow(2, 43, 431) == pow(3, 43, 431) == 1


def check_rational_prime_scale():
    """Bound the Mertens constant by its absolutely convergent series."""
    from decimal import Decimal, localcontext

    bound = 10**6
    scale = 10**16
    cutoff = 40
    primes = primes_below(bound + 1)
    harmonic = sum(scale // j for j in range(1, bound + 1))
    negative_sum = sum(scale // (k * p**k)
                       for p in primes for k in range(2, cutoff + 1))
    with localcontext() as ctx:
        ctx.prec = 60
        d = Decimal
        # Decimal.ln is correctly rounded; the slack exceeds all 60-digit errors.
        slack = d("1e-45")
        log_bound = d(bound).ln()
        gamma_low = d(harmonic) / scale - log_bound - 1 / d(bound) - slack
        gamma_high = d(harmonic + bound) / scale - log_bound + slack
        # B = gamma - sum_p sum_{k>=2} 1/(k p^k).  The omitted prime
        # tail is bounded by sum_{j>bound} 1/(2j(j-1))=1/(2*bound).
        # The k-tail for each retained prime is <= 2^(-cutoff).
        tail = d(1)/(2*bound) + d(len(primes))/(2**cutoff)
        term_count = (cutoff - 1) * len(primes)
        b_low = gamma_low - d(negative_sum + term_count) / scale - tail - slack
        b_high = gamma_high - d(negative_sum) / scale + slack
        assert b_low > d("0.261496") and b_high < d("0.261499")
        x_low, x_high = d("6.51e81"), d("6.57e81")
        z, Z = x_low.ln(), x_high.ln()
        assert z.ln() + b_high + 1/(2*z*z) + slack < d("5.5")
        assert Z.ln() + b_low - 1/(2*Z*Z) - slack > d("5.5")
        assert x_low/z * (1 + 1/(2*z)) > d("3.46e79") * (1+slack)
        assert x_high/Z * (1 + 3/(2*Z)) < d("3.52e79") * (1-slack)
        print("degree 1     3.46e79 < coordinates < 3.52e79")


if __name__ == "__main__":
    check_rational_prime_scale()
