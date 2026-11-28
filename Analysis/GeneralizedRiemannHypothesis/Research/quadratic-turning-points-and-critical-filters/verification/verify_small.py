#!/usr/bin/env python3
"""Certified all-order signs for the primitive quadratic conductors below 512.

Python >= 3.9, standard library only.  Output to stdout is a CSV table.
All interval endpoints after evaluating exponentials are scaled integers.
No sign decision uses floating-point arithmetic.
"""
import csv
import functools
import math
import sys
from fractions import Fraction
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR

S = 1 << 576
MAX_H = 1 << 15
N = 256
U = 6
E_SCALE = 10**18     # absolute error <= 1/E_SCALE outside the finite sum/integral
LOW = Context(prec=55, rounding=ROUND_FLOOR)
HIGH = Context(prec=55, rounding=ROUND_CEILING)
PI_LO = Decimal("3.14159265358979323846264338327950288419716939937510")
PI_HI = Decimal("3.14159265358979323846264338327950288419716939937511")


def check_pi_enclosure():
    """Machin's identity with alternating arctangent-series bounds."""
    def atan_bounds(n):
        a = sum(Fraction((-1)**j, (2*j+1)*n**(2*j+1)) for j in range(50))
        return a, a + Fraction(1, 101*n**101)

    lo5, hi5 = atan_bounds(5)
    lo239, hi239 = atan_bounds(239)
    assert Fraction(PI_LO) < 16*lo5 - 4*hi239
    assert 16*hi5 - 4*lo239 < Fraction(PI_HI)


def ceil_div(x, y):
    return -((-x) // y)


def bounds_product(a, b, c, d):
    vals = (a*c, a*d, b*c, b*d)
    return min(vals), max(vals)


def exp_ends(a, b):
    # Decimal.exp is correctly rounded to nearest. Move one number outward.
    return LOW.next_minus(LOW.exp(a)), HIGH.next_plus(HIGH.exp(b))


def fixed(a, b):
    return (int(LOW.multiply(a, S).to_integral_value(rounding=ROUND_FLOOR)),
            int(HIGH.multiply(b, S).to_integral_value(rounding=ROUND_CEILING)))


@functools.lru_cache(maxsize=None)
def grid_data(i, parity):
    u = LOW.divide(i, MAX_H)     # Exact dyadic, <=6, represented in 55 digits.
    t = LOW.multiply(2, u)
    e2l, e2h = exp_ends(t, t)
    v = LOW.multiply(u, Decimal('1.5') if parity else Decimal('0.5'))
    el, eh = fixed(*exp_ends(v, v))
    return LOW.multiply(PI_LO, e2l), HIGH.multiply(PI_HI, e2h), el, eh


def is_squarefree(n):
    return all(n % (a*a) for a in range(2, math.isqrt(n)+1))


def fundamental(D):
    if D % 4 == 1:
        return is_squarefree(abs(D))
    return D % 4 == 0 and (D//4) % 4 in (2, 3) and is_squarefree(abs(D)//4)


def kronecker(D, n):
    # Kronecker symbol with positive denominator.
    ans = 1
    while n % 2 == 0:
        if D % 2 == 0:
            return 0
        if D % 8 in (3, 5):
            ans = -ans
        n //= 2
    a = D % n
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                ans = -ans
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            ans = -ans
        a %= n
    return ans if n == 1 else 0


def verify_character(D, seed):
    q = abs(D)
    coeff = [0]+[kronecker(D, n)*(n if D < 0 else 1) for n in range(1, N+1)]
    node_cache = {}

    def node(i):
        if i in node_cache:
            return node_cache[i]
        c0, c1, el, eh = grid_data(i, D < 0)
        arg0 = HIGH.divide(c1, q).copy_negate()
        arg1 = LOW.divide(c0, q).copy_negate()
        al, ah = fixed(*exp_ends(arg0, arg1))
        al, ah = max(0, al), min(S, ah)
        sl, sh = (al*al)//S, ceil_div(ah*ah, S)
        # x_n = a^(n^2); r_n = a^(2n+1).
        xl, xh = al, ah
        rl, rh = (al*sl)//S, ceil_div(ah*sh, S)
        pl = ph = nl = nh = 0
        for n in range(1, N+1):
            if xh <= 2:
                rem = (N-n+1)*(N+n)  # upper bound 2 sum_{n<=j<=N} j
                ph += rem
                nh += rem
                break
            c = coeff[n]
            if c >= 0:
                pl += c*xl
                ph += c*xh
            else:
                nl += (-c)*xl
                nh += (-c)*xh
            xl, xh = (xl*rl)//S, ceil_div(xh*rh, S)
            rl, rh = (rl*sl)//S, ceil_div(rh*sh, S)
        node_cache[i] = (pl, ph, nl, nh, el, eh)
        return node_cache[i]

    # A positive theta tail starts at A.
    # The thresholds ensure exp(2*A) >= q/8.
    A = 1 if q <= 56 else (2 if q <= 432 else 3)
    todo = list(range(seed+1))
    out = {}
    H = 8
    while todo:
        if H > MAX_H:
            raise ArithmeticError(f'Increase MAX_H for {D}: {todo}')
        stride = MAX_H//H
        sums = {m:[0,0] for m in todo}
        left = node(0)
        for j in range(U*H):
            right = node((j+1)*stride)
            # Positive and negative Gaussian subsums decrease separately.
            a = right[0] - left[3]
            b = left[1] - right[2]
            kl, kh = bounds_product(a, b, left[4], right[5])
            kl, kh = kl//S, ceil_div(kh, S)
            gl, gh = bounds_product(kl, kh, j*j-H*H, (j+1)**2-H*H)
            for m in todo:
                g0, g1 = gl, gh
                if m == seed and j < A*H:
                    # The negative part gives the signed dominance test.
                    g0, g1 = min(0, g0), min(0, g1)
                lo, hi = bounds_product(g0, g1, j**(2*m), (j+1)**(2*m))
                sums[m][0] += lo
                sums[m][1] += hi
            left = right
        for m in todo:
            den = S*H**(2*m+3)
            lo, hi = sums[m]
            # Unit of reported enclosure is 10^(-12). Outward rounding.
            il = (10**12*(lo*E_SCALE-den))//(den*E_SCALE)
            ih = ceil_div(10**12*(hi*E_SCALE+den), den*E_SCALE)
            if il > 0 or ih < 0:
                out[m] = (D,m,H,il,ih)
        todo = [m for m in todo if m not in out]
        H *= 2
    if out[seed][3] <= 0:
        raise ArithmeticError(f'Nonpositive dominance bound for D={D} at m={seed}')
    return [out[m] for m in sorted(out)]


SEED = 16


def main():
    check_pi_enclosure()
    out = csv.writer(sys.stdout, lineterminator='\n')
    out.writerow(['D', 'm', 'integral', 'cells_per_unit',
                  'lower_times_1e12', 'upper_times_1e12'])
    for q in range(3, 512):
        for D in (q, -q):
            if fundamental(D):
                rows = verify_character(D, seed=SEED)
                signs = [row[3] > 0 for row in rows]
                if signs != sorted(signs):
                    raise AssertionError(f'Unexpected sign pattern at D={D}')
                for d, m, h, lo, hi in rows:
                    kind = 'tail_seed' if m == SEED else 'difference'
                    out.writerow([d, m, kind, h, lo, hi])
                sys.stdout.flush()


if __name__ == '__main__':
    main()
