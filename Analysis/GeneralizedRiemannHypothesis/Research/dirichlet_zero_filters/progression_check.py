#!/usr/bin/env python3
"""Certify zero-free intervals for explicit trigonometric polynomials.

Run with Python 3.9+. All choices, inequalities and displayed decimal
roundings are verified with integer or rational arithmetic. Positive
values at sample points are not used. See verify() for the inequalities.
"""

from fractions import Fraction as Q


def atan_inverse_bounds(n, pairs=6):
    """Rational lower/upper bounds for arctan(1/n) by the alternating series."""
    t = Q(1, n)
    lower = sum((-1)**j * t**(2*j + 1) / (2*j + 1)
                for j in range(2*pairs))
    return lower, lower + t**(4*pairs + 1) / (4*pairs + 1)


# Machin's identity pi = 16 atan(1/5) - 4 atan(1/239).
lo5, hi5 = atan_inverse_bounds(5)
lo239, hi239 = atan_inverse_bounds(239)
PI_LO = 16*lo5 - 4*hi239


def exp_lower(t):
    """Taylor lower bound for exp(t), t >= 0."""
    total = term = Q(1)
    for j in range(1, 21):
        term *= t/j
        total += term
    return total


def decimal_bound(value, digits, upward=False):
    """Directed decimal rounding of a nonnegative rational."""
    n = value.numerator * 10**digits
    d = value.denominator
    units = (n+d-1)//d if upward else n//d
    whole, frac = divmod(units, 10**digits)
    return f"{whole}.{frac:0{digits}d}"


def ceil(value):
    return -(-value.numerator // value.denominator)


def verify(beta, k, damping, trim, tail_power):
    """Certify Re[e^(-i pi c beta+i beta t) P_K(e^(it))] > 0 throughout.

    Here alpha=2 beta, c=ceil(1/alpha), rho=1-D/(K+2),
    P_K(z)=sum_{j=0}^K ((alpha)_j/j!) rho^j z^j. The interval in t is
    [delta,2 pi c-delta], delta=trim/(K+2); D is called 'damping'.

    For the untruncated expression the phase derivative is positive. After
    rotation its endpoint phase margin to the imaginary axis is
      pi(1/2-(c-1)beta) - alpha atan((1-rho)/(1+rho) cot(delta/2)).
    Hence the following rational 'margin' is a strict lower bound, by
    tan(delta/2) >= delta/2 and atan(v) <= v. The sine is at least
    margin-margin^3/6 on [0,pi/2]. The relative Taylor tail bound raised
    to denominator(alpha) is at most 'tail_power', as computed below.
    """
    alpha = 2*beta
    c = ceil(1/alpha)
    rho = 1 - damping/(k+2)
    delta = trim/(k+2)
    if not (0 < rho < 1 and 0 < delta < PI_LO):
        return False
    margin = PI_LO*(Q(1, 2)-(c-1)*beta) - 2*alpha*(1-rho)/((1+rho)*delta)
    if margin <= 0:
        return False
    lower_sine = margin - margin**3/6
    return lower_sine**alpha.denominator > tail_power


def search(beta, k):
    """Select the least certified trim on a grid, over a finite list of D."""
    alpha = 2*beta
    best = None
    for d16 in range(16, 129):
        damping = Q(d16, 16)
        if damping >= k+2:
            continue
        exponent = (k+1)*damping/(k+2)
        # |remainder/full| <= 2 rho^(K+1) / D^(1-alpha).
        # This follows by summation by parts and
        # (alpha)_j/j! <= (j+1)^(alpha-1).
        relative = 2 / exp_lower(exponent)
        tail_power = (relative**alpha.denominator /
                      damping**(alpha.denominator-alpha.numerator))
        # Search trim=n/100, restricting to delta<pi so the test is monotone.
        left, right = 0, min(20000, int(PI_LO*(k+2)*100)-1)
        if not verify(beta, k, damping, Q(right, 100), tail_power):
            continue
        while right-left > 1:
            mid = (left+right)//2
            if verify(beta, k, damping, Q(mid, 100), tail_power):
                right = mid
            else:
                left = mid
        candidate = (Q(right, 100), damping)
        if best is None or candidate < best:
            best = candidate
    if best is None:
        raise ArithmeticError("The parameter grid did not certify an interval")
    return best


def main():
    print("Certified bounds on b M, with frequencies N+j b for 0<=j<=K.")
    print("D sets rho=1-D/(K+2), and U sets delta=U/(K+2) in radians.")
    print("Both bounds are rounded outwards. The lower witness is strictly positive.")
    print(" N  b     K       D        U        lower bM        upper bM")
    for n, b in [(1, 3), (2, 5), (2, 7)]:
        beta = Q(n, b)
        c = ceil(1/(2*beta))
        for k in (64, 256, 1024):
            trim, damping = search(beta, k)
            lower = c - trim/((k+2)*PI_LO)
            upper = c - (2*beta*c-1)/(k+2*beta)
            if not 0 < lower < upper < c:
                raise ArithmeticError("Unexpected witness or upper bound")
            print(f"{n:2d} {b:2d} {k:5d}  {str(damping):>6}  {str(trim):>7}"
                  f"      {decimal_bound(lower, 8)}      {decimal_bound(upper, 8, True)}")


if __name__ == "__main__":
    main()
