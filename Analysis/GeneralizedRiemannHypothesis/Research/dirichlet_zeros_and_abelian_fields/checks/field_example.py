#!/usr/bin/env python3
"""Reproduce the finite-height biquadratic-field certificate using rational arithmetic.

Run python3 field_example.py to print the certificate. All inequalities used
to certify the result compare integers or rational numbers. The input
zero-count theorem is Bennett, Martin, O'Bryant and Rechnitzer, Math.
Comp. 90 (2021), Corollary 1.2, https://arxiv.org/abs/2005.02989 .
"""

from fractions import Fraction as F
from math import comb, factorial, isqrt


def exp_lower(x, degree=32):
    """Lower bound for exp(x) for a positive rational x."""
    assert x > 0
    return sum(x**n / factorial(n) for n in range(degree + 1))


def derivative_l2_squared(k, j):
    """Twice the squared L2 norm of derivative j of phi=(x(1-x*x)^k)'."""
    assert 1 <= j <= k - 1
    terms = []
    for i in range(k + 1):
        if 2 * i >= j:
            coefficient = ((-1)**i * comb(k, i) * (2*i + 1)
                           * factorial(2*i) // factorial(2*i - j))
            terms.append((2*i - j, coefficient))
    # Products have even degree; their integrals on [-1,1] are 2/(degree+1).
    return 4 * sum(F(c*d, m+n+1) for m, c in terms for n, d in terms)


def integer_sqrt_upper(x):
    lo = isqrt(x.numerator // x.denominator)
    return lo if lo**2 == x else lo + 1


def negative_moment_bound(H, j, log_envelope_main, log_envelope_error):
    """Upper bound for sum_{f, |gamma|>H} |gamma|^(-j), counting both signs."""
    # Sum of the four smooth zero-count main terms is
    # A(t)=(4t/pi)log(sqrt(1105)t/(2*pi*e)).  BMOR Corollary 1.2 bounds
    # the absolute error by E(t)=(6/5)log(34t)+18 since sqrt(1105)<34.
    # Partial summation gives integral A'(t)t^-j plus
    # E(H)H^-j + j*integral E(t)t^(-j-1).  Also 4/pi<32/25,
    # and sqrt(1105)/(2*pi)<17/3.
    assert exp_lower(log_envelope_main) > F(17*H, 3)
    assert exp_lower(log_envelope_error) > 34*H
    main = F(32, 25*(j-1)) * F(H)**(1-j) * (log_envelope_main + F(1, j-1))
    error = F(H)**(-j) * (F(12, 5)*log_envelope_error + F(6, 5*j) + 36)
    return main + error


def main():
    # The common factors are zeta and chi_1105. All four remaining
    # factors are primitive, real, and even. At 3 the quadratic character
    # chi_D(3) is +1 or -1 according as D mod 3 is 1 or 2.
    field_k = (5, 221)
    field_l = (13, 85)
    assert 5 * 221 == 13 * 85 == 1105
    chi_k = tuple(1 if d % 3 == 1 else -1 for d in field_k)
    chi_l = tuple(1 if d % 3 == 1 else -1 for d in field_l)
    assert chi_k == (-1, -1) and chi_l == (1, 1)

    # For a=2/7 the packet centered at log(3) meets no other log(n),
    # n>=2: log(4/3)=2*atanh(1/7)>2/7.
    a, k, j = F(2, 7), 7, 6
    norm_squared = derivative_l2_squared(k, j)
    norm_upper = integer_sqrt_upper(norm_squared)
    fourier_upper = a**(1-j) * norm_upper
    # log(3)=2*atanh(1/2)>1+1/12+1/80; sqrt(3)<7/4.
    assert F(7, 4)**2 > 3
    main_lower = 4*(1 + F(1, 12) + F(1, 80))/F(7, 4)
    assert main_lower > F(5, 2)

    print("Shared zeta factors: zeta(s), L(s, chi_1105)")
    print("At 3: (chi_5, chi_221, chi_13, chi_85) =", chi_k + chi_l)
    print(f"Packet: a={a}, k={k}, derivative order j={j}")
    print("2*integral_-1^1 (phi^(j))^2 =", norm_squared)
    print("Upper bound for |t|^j |g_hat(t)| =", fourier_upper)
    print("Lower bound for the full spectral contrast =", main_lower)
    H = 45
    moment = negative_moment_bound(H, j, F(28, 5), F(37, 5))
    tail = fourier_upper * moment
    assert tail < F(12, 5) < main_lower
    print(f"H={H}: upper bound for the negative zero moment =", moment)
    print(f"H={H}: upper bound for the absolute four-function tail =", tail)
    print("The tail is < 12/5, and the full contrast is > 5/2.")
    print("Conclusion: a positive ordinate with unequal multiplicities occurs by height 45.")

    # An optional stronger count at a moderately larger height.
    # integral |phi(x)| dx = 4*(14/15)^7/sqrt(15) by monotonicity of
    # x(1-x^2)^7 up to x=1/sqrt(15).  Count a conjugate pair by 2*||g||_1.
    H = 80
    tail = fourier_upper * negative_moment_bound(H, j, F(31, 5), F(8))
    assert F(19, 5)**2 < 15
    paired_upper = 2 * a * 4 * F(5, 19) * F(14, 15)**7
    assert main_lower - tail > 6 * paired_upper
    print(f"H={H}: upper bound for the absolute tail =", tail)
    print(f"H={H}: at least 7 units of absolute excess multiplicity at positive ordinates.")


if __name__ == "__main__":
    main()
