"""Reproduce two finite checks of factorial.tex, using only Python's standard library."""
from cmath import exp
from math import factorial, fsum, isqrt, log, sqrt


def prime_powers(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start::p] = bytes((limit - start) // p + 1)
    entries = []
    for p in range(2, limit + 1):
        if sieve[p]:
            power = p
            while power <= limit:
                entries.append((power, log(p)))
                power *= p
    return entries


def chi3(n):
    return (0, 1, -1)[n % 3]


def finite_arithmetic_check():
    """Compare the mod-3 primitive character and its lift modulo 15."""
    entries = prime_powers(factorial(9))
    print("Finite prime-power data")
    print(" k          k!        B_mod3      B_mod15  lift difference")
    for k in range(2, 10):
        x = factorial(k)
        base = fsum(weight * chi3(m) * (1 - m / x)
                    for m, weight in entries if m <= x) / sqrt(x)
        lift = fsum(weight * chi3(m) * (1 - m / x)
                    for m, weight in entries if m <= x and m % 5) / sqrt(x)
        # Only the removed powers of 5 contribute to the difference.
        powers = []
        m = 5
        while m <= x:
            powers.append(log(5) * chi3(m) * (1 - m / x))
            m *= 5
        difference = fsum(powers) / sqrt(x)
        assert abs((base - lift) - difference) < 1e-13
        assert abs(base - lift) <= log(x) / sqrt(x)
        print(f"{k:2d}  {x:10d}  {base:12.8f} {lift:12.8f} {base-lift:15.8f}")


def finite_spectrum_check():
    """Compare a synthetic two-mode lag average with the theorem's diagonal term."""
    modes = [(0.71, 0.8 - 0.3j), (-1.3, 0.5 + 0.2j)]
    checkpoints = {1000, 10000, 100000}
    print("\nTwo-mode model, h=1 (frequencies are synthetic)")
    print("     N        |C(N)|    |predicted|   |difference|")
    log_fact = 0.0
    value = sum(coefficient for _, coefficient in modes)
    total = 0j
    for n in range(1, max(checkpoints) + 1):
        log_fact += log(n + 1)
        next_value = sum(coefficient * exp(1j * t * log_fact)
                         for t, coefficient in modes)
        total += next_value * value.conjugate()
        value = next_value
        if n in checkpoints:
            predicted = sum(abs(coefficient) ** 2 * exp(1j * t * log(n)) / (1 + 1j * t)
                            for t, coefficient in modes)
            mean = total / n
            print(f"{n:6d}    {abs(mean):11.8f}   {abs(predicted):11.8f}  {abs(mean-predicted):13.8f}")
    assert abs(mean - predicted) < 0.02


if __name__ == "__main__":
    finite_arithmetic_check()
    finite_spectrum_check()
