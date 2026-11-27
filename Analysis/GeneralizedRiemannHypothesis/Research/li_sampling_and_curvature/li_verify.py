#!/usr/bin/env python3
"""Exact finite illustrations of joint polynomial recurrence for Li sums.

The checks use only Python's standard library and exact integers or rational numbers.
"""

from math import gcd
from fractions import Fraction as Q


def gauss_mul(v, w):
    a, b = v
    c, d = w
    return a*c - b*d, a*d + b*c


def gauss_pow(v, n):
    result = (1, 0)
    while n > 0:
        if n % 2 == 1:
            result = gauss_mul(result, v)
        v = gauss_mul(v, v)
        n //= 2
    return result


def cayley_inverse(z):
    """rho=1/(1-z) in exact Gaussian rational arithmetic."""
    a, b = z
    norm = (1-a)**2 + b*b
    return (1-a)/norm, b/norm


def li_cyclotomic(q, radius, n):
    """Two circles R and R^-1 over all nontrivial qth roots of unity."""
    character_sum = q - 1 if n % q == 0 else -1
    return 2 * (q - 1) - character_sum * (radius**n + radius**(-n))


def cyclotomic_check():
    q, radius = 3, Q(6, 5)
    values = {n: li_cyclotomic(q, radius, n) for n in range(1, 62)}
    assert all((value < 0) == (n % q == 0) for n, value in values.items())
    pairs = list(range(1, 61))
    common = [k for k in pairs if values[k] < 0 and values[k+1] < 0]
    assert not common
    print("Cyclotomic obstruction (q=3, R=6/5).")
    print("  For n=1..61 the negative indices are precisely the multiples of 3.")
    for n in range(1, 4):
        print(f"  lambda_{n} = {values[n]}")
    print("  For k=1..60, no pair (k,k+1) gives two negative sums.")
    print("  Individually, each of k and k+1 has a root modulo every q.")


def sample_rational_spectrum():
    """Spectrum z = R^+-1 (3 +- 4i)/5, R=6/5."""
    radius = Q(6, 5)
    phases = [(Q(3, 5), Q(4, 5)), (Q(3, 5), -Q(4, 5))]
    zeros = {cayley_inverse((r*a, r*b)) for r in (radius, 1/radius)
             for a, b in phases}
    assert zeros == {(a, b) for a in (Q(7,25), Q(18,25))
                     for b in (Q(24,25), -Q(24,25))}
    assert {(1-a, b) for a,b in zeros} == zeros
    assert {(a, -b) for a,b in zeros} == zeros
    print("Off-line rational zeros: 7/25 +/- (24/25)i and 18/25 +/- (24/25)i.")
    print("  The Cayley parameters have radii 6/5 and 5/6.")

    # Normalized value lambda_n/R^n =
    # 4 (5/6)^n - 2 (1+(5/6)^(2n)) Re((3+4i)/5)^n.
    def normalized_li(n):
        re, _ = gauss_pow((3,4), n)
        return 4/radius**n - 2*(1+radius**(-2*n))*Q(re,5**n)

    indices = range(1, 65)
    k_values = {k: normalized_li(k) for k in indices}
    square_values = {k: normalized_li(k*k) for k in indices}
    for threshold in (0, Q(-3, 2)):
        good = [k for k in indices
                if max(k_values[k], square_values[k]) < threshold]
        assert good
        print(f"  k,k^2 with both normalized sums < {threshold} "
              f"for 1 <= k <= 64: {len(good)}; indices {good}.")


def polynomial_check():
    """A jointly intersective family without a common integer root."""
    def f(n):
        return (n*n - 13)*(n*n - 17)*(n*n - 221)
    roots = {}
    for q in range(1, 101):
        roots[q] = next((n for n in range(q) if
                         gcd(n, q) == 1 and f(n) % q == (n+2)*f(n) % q == 0), None)
        assert roots[q] is not None
    # The general all-q claim is obtained by Hensel and CRT. Finite checks
    # here only illustrate it. The three constants are all positive nonsquares.
    print("Joint modular roots of F and (X+2)F, F=(X^2-13)(X^2-17)(X^2-221).")
    print("  Every modulus q<=100 passes; sample least common unit roots:",
          {q: roots[q] for q in (8, 13, 17, 45, 64, 91, 100)})


def line_pair_check():
    def li(n):
        re, _ = gauss_pow((3,4), abs(n))
        return 2*(1-Q(re,5**abs(n)))
    ceiling = Q(8,5)
    for n in range(40):
        curvature = li(n+1) - 2*li(n) + li(n-1)
        assert curvature == ceiling * (1-li(n)/2)
        assert curvature <= ceiling
    print("On-line conjugate pair with Re(z)=3/5: curvature identity holds")
    print("  through n=39, with exact ceiling 8/5.")


def main():
    if not __debug__:
        raise RuntimeError("Run Python without -O so all checks are enabled.")
    cyclotomic_check()
    sample_rational_spectrum()
    polynomial_check()
    line_pair_check()


if __name__ == "__main__":
    main()
