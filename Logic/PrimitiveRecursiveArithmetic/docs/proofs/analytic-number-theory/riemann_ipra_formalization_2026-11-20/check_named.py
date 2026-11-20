"""Exact finite arithmetic checks for RobinNicolas.lean. No floating-point comparisons."""
from fractions import Fraction as Q
from math import factorial, isqrt, prod


def panels(x, m, upper):
    """Independent direct quadrature using reduced Fraction arithmetic."""
    x = max(x, Q(1))
    h = (x - 1) / m
    return h * sum((1 / (1 + (j + (not upper)) * h) for j in range(m)), Q(0))


def compiled_panels(a, b, m, upper):
    """Cross-check the source's unreduced common-denominator integer formula."""
    t = max(a, b) - b
    dens = [b * m + j * t for j in range(m + 1)]
    D = prod(dens)
    use = dens[:-1] if upper else dens[1:]
    return Q(t * sum(D // den for den in use), D)


def log_integer(n, m, upper):
    e = n.bit_length() - 1
    return e * panels(Q(2), m, upper) + panels(Q(n, 2**e), m, upper)


def gamma_pair(m, upper):
    h = sum((Q(1, i) for i in range(1, m + 1)), Q(0))
    r = 2 * m
    if upper:
        return Q(1, m) / (1 - h/r)**r
    return (1 + h/r)**r / (m + 1)


def threshold(n, m, upper):
    return gamma_pair(m, upper) * panels(log_integer(n, m, upper), m, upper)


def reference_gamma():
    # H_K - log(K+1) < gamma < H_K - log(K).
    # Independently enclose exp(H_K) via its ordinary Taylor series.
    K = 128
    h = sum((Q(1, i) for i in range(1, K + 1)), Q(0))
    B = 36
    partial = sum((h**k / factorial(k) for k in range(B)), Q(0))
    tail = (h**B / factorial(B)) / (1 - h/(B+1))
    return partial / (K+1), (partial + tail) / K


def reference_log(x):
    """Independent log interval using the artanh series after range reduction."""
    assert x >= 1
    e = max(0, x.numerator.bit_length() - x.denominator.bit_length())
    if x < 2**e:
        e -= 1

    def atanh(t):
        z = (t-1)/(t+1)
        B = 14
        p = 2*sum((z**(2*k+1)/(2*k+1) for k in range(B)), Q(0))
        return p, p + 2*z**(2*B+1) / ((2*B+1)*(1-z*z))

    left = atanh(Q(2))
    right = atanh(x / 2**e)
    return tuple(e*left[k] + right[k] for k in (0, 1))


def sigma(n):
    return sum(i for i in range(1, n+1) if n % i == 0)


def is_prime(n):
    return n >= 2 and all(n % j for j in range(2, isqrt(n)+1))


def signs(n, target, m):
    lo, hi = [threshold(n, m, upper) for upper in (False, True)]
    L = log_integer(n, m, False)
    up = max(Q(0), target-hi)**2 * L
    down = max(Q(0), lo-target)**2 * L
    return lo, hi, up, down


def main():
    gl, gu = reference_gamma()
    for m in (1, 2, 3, 5, 8, 16, 32):
        assert gamma_pair(m, False) < gl <= gu < gamma_pair(m, True)
        for x in (Q(1), Q(17, 13), Q(2), Q(15, 4), Q(1234, 77)):
            lo, hi = reference_log(x)
            for upper, ref in ((False, lo), (True, hi)):
                q = panels(x, m, upper)
                assert q == compiled_panels(x.numerator, x.denominator, m, upper)
                assert q >= ref if upper else q <= ref

    for n in (6, 30, 210, 5041, 5042):
        nl, nu = reference_log(Q(n))
        ll = reference_log(nl)[0]
        lu = reference_log(nu)[1]
        for m in (1, 3, 8):
            assert log_integer(n, m, False) <= nl <= nu <= log_integer(n, m, True)
            assert threshold(n, m, False) <= gl * ll <= gu * lu <= threshold(n, m, True)

    # Certify strict margins on samples using rational endpoint arithmetic.
    for n in (5041, 5042, 5053):  # 5040 is deliberately outside Robin's domain
        target = Q(sigma(n), n)
        assert target <= threshold(n, 1, True)
        first = next(m for m in range(1, 33) if target < threshold(n, m, False))
        print(f"Robin n={n} first strict grid certificate m={first}")

    for y in (3, 4, 5, 7, 11):
        primes = [p for p in range(2, y+1) if is_prime(p)]
        P = prod(primes)
        target = Q(P, prod(p-1 for p in primes))
        first = None
        for m in range(1, 33):
            lo, hi, up, down = signs(P, target, m)
            assert lo <= target and up <= 25 and down <= 25
            if hi < target:
                first = m
                break
        print(f"Nicolas y={y}, primorial={P}, first strict grid certificate m={first}")
        assert first is not None
    print("Exact gamma, log, margin and scaled-error sample checks passed.")


if __name__ == "__main__":
    main()
