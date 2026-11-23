"""Certify both sides of the Catalan estimates against independent pi brackets."""
from fractions import Fraction
from math import comb


def verify_wallis():
    # An even truncation of Gregory's series is a lower bound. The next
    # truncation is an upper bound. Both computations stay rational.
    terms = 512
    lower_pi = 4 * sum(Fraction((-1)**j, 2*j + 1) for j in range(terms))
    upper_pi = lower_pi + Fraction(4, 2*terms + 1)
    for n in range(1, 101):
        a = Fraction(4**n, comb(2*n, n))
        wallis_lower = 2*a*a / (2*n + 1)
        wallis_upper = a*a / n
        assert wallis_lower <= lower_pi <= upper_pi <= wallis_upper
        assert wallis_upper - wallis_lower <= Fraction(4, 2*n + 1)

        # Squared relative estimates, all endpoints nonnegative.
        central_scale = n / (a*a)
        central_lower = 1 - Fraction(1, 4*n)
        assert central_lower**2 <= lower_pi*central_scale
        assert upper_pi*central_scale <= 1

        catalan_scale = n**3 / (a*a*(n+1)**2)
        catalan_lower = 1 - Fraction(5, 4*(n+1))
        assert catalan_lower**2 <= lower_pi*catalan_scale
        assert upper_pi*catalan_scale <= 1


if __name__ == "__main__":
    verify_wallis()
    print("PASS: rational Wallis, central binomial, and Catalan bounds for 1 <= n <= 100")
