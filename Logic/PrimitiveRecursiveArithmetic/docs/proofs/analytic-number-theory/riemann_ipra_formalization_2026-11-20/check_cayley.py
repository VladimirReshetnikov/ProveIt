"""Cross-check the signed integer Cayley numerator against fraction composition."""
from fractions import Fraction
from math import comb, factorial, lcm


def taylor_samples(m, N):
    bits = [0]
    product = 1
    for n in range(1, N + 1):
        product = lcm(product, n)
        bits.append(product.bit_length() - 1)
    delta = [0] + [bits[n] - bits[n - 1] for n in range(1, N + 1)]
    jump = [delta[n] - (0 if n % 2 else 2 * delta[n // 2]) for n in range(N + 1)]
    J = [sum(N**2 // (N + i) for i in range(1, N * (n - 1) + 1)) for n in range(N + 1)]
    fac_N = factorial(N)
    A = [
        sum(jump[n] * J[n]**k * (fac_N // n)**5 for n in range(1, N + 1))
        for k in range(m + 1)
    ]
    return A, [Fraction(a, factorial(k) * N**(2 * k) * fac_N**5) for k, a in enumerate(A)]


def compose(samples):
    # Horner substitution of -9 z/(1-z) through the requested degree.
    m = len(samples) - 1
    p = [Fraction(0)] * (m + 1)
    for sample in reversed(samples):
        p = [sample] + [-9 * sum(p[:i]) for i in range(1, m + 1)]
    return p[-1]


def compare(m, N):
    A, samples = taylor_samples(m, N)
    integer = sum(
        (-9)**k * comb(m - 1, k - 1) * (factorial(m) // factorial(k)) * N**(2 * (m - k)) * A[k]
        for k in range(1, m + 1)
    )
    D = factorial(m) * N**(2 * m) * factorial(N)**5
    result = Fraction(integer, D)
    assert result == compose(samples)
    assert sum(9**k * comb(m - 1, k - 1) for k in range(1, m + 1)) == 9 * 10**(m - 1)
    return result


if __name__ == "__main__":
    for n in range(1, 13):
        for order in range(1, 8):
            compare(order, n)
    print("84 integer numerator, rational composition, and weight-sum comparisons passed")
    print("N=3, m=1,2,3:", *[compare(m, 3) for m in (1, 2, 3)])
