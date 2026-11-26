#!/usr/bin/env python3
"""A zero-free rectangle for the conductor-23 eta Mellin transform, using integer bounds."""
from fractions import Fraction as F

S = 2**40
NU = 1024                   # u subdivisions per unit
NT = 256                    # t subdivisions per unit
NA = 512                    # cos table indices per radian


def ceildiv(a, b):
    return -((-a) // b)


def up_product(x, y):
    return ceildiv(x*y, S)


def down_product(x, y):
    return x*y // S


def exp_bounds(x):
    """Return integer bounds scaled by S on exp(x), for rational 0 <= x <= 128."""
    y = F(x, 128)
    assert 0 <= y <= 1
    term = F(1)
    taylor = term
    for n in range(1, 15):
        term *= y/n
        taylor += term
    more = 2*term*y/15      # remaining terms have successive ratio <= 1/16
    lo = int(S*taylor)
    hi = ceildiv((taylor+more).numerator*S, (taylor+more).denominator)
    for _ in range(7):
        lo, hi = down_product(lo, lo), up_product(hi, hi)
    return lo, hi


def check_constants():
    # Machin's formula and the alternating arctangent series.
    def atan_interval(q):
        partial = sum(F((-1)**n, (2*n+1)*q**(2*n+1)) for n in range(8))
        return partial, partial + F(1, 17*q**17)
    low5, high5 = atan_interval(5)
    low239, high239 = atan_interval(239)
    pi_lo, pi_hi = 16*low5-4*high239, 16*high5-4*low239
    assert 23*F(13101,10000)**2 < 4*pi_lo**2
    assert 4*pi_hi**2 < 23*F(13102,10000)**2
    # Tail exp(-exp(4)) < exp(-48) < 2^-64, since exp(3/4)>2.
    assert exp_bounds(4)[0] > 48*S and exp_bounds(F(3,4))[0] > 2*S


def cosine_lower_table():
    # The cosine Taylor polynomial ending at degree 62 is a lower bound
    # everywhere (integrate 1-cos(x)>=0 repeatedly). We use rational Horner.
    table = []
    for i in range(16*NA+1):
        v = F(i*i, NA*NA)
        h = F(1)
        for j in range(31, 0, -1):
            h = 1 - v*h/(2*j*(2*j-1))
        table.append((S*h.numerator)//h.denominator)
    return table


def weights():
    """For cell j, return lo(K), hi(K cosh(u/2)), scaled by S."""
    out = []
    exp_u = [exp_bounds(F(j, NU)) for j in range(4*NU+1)]
    exp_half = [exp_bounds(F(j, 2*NU)) for j in range(4*NU+1)]
    for j in range(4*NU):
        # 1.3101 < 2*pi/sqrt(23) < 1.3102. K = exp(u/2) q prod(1-q^n)(1-q^(23n)).
        x_lo = F(13101*exp_u[j][0], 10000*S)
        x_hi = F(13102*exp_u[j+1][1], 10000*S)
        q_lo = S*S // exp_bounds(x_hi)[1]
        q_hi = ceildiv(S*S, exp_bounds(x_lo)[0])
        # Truncate first product at n=8. Bound both discarded product tails
        # by one minus the sum of all their omitted powers of q.
        plo = phi = S
        power_lo = power_hi = S
        for _ in range(8):
            power_lo = down_product(power_lo, q_lo)
            power_hi = up_product(power_hi, q_hi)
            plo = down_product(plo, S-power_hi)
            phi = up_product(phi, S-power_lo)
        next_q = up_product(power_hi, q_hi)
        # 23 >= 9, hence q^23/(1-q^23) <= q^9/(1-q).
        tail = ceildiv(2*next_q*S, S-q_hi)
        plo = down_product(plo, S-tail)
        klo = down_product(down_product(exp_half[j][0], q_lo), plo)
        khi = up_product(up_product(exp_half[j+1][1], q_hi), phi)
        e = exp_half[j+1]
        cosh_hi = ceildiv(e[1] + ceildiv(S*S,e[0]),2)
        out.append((klo,up_product(khi,cosh_hi)))
    return out


def main():
    check_constants()
    w = weights()
    cos_lo = cosine_lower_table()
    minimum = None
    # Each phase lies between t_lo*u_lo and t_hi*u_hi. Use |cos'|<=1
    # between this phase and the table point floor(NA*t_lo*u_lo)/NA.
    for k in range(4*NT):
        acc = 0
        for j,(lo,hi) in enumerate(w):
            idx = NA*k*j//(NT*NU)
            err = ceildiv(S*((k+1)*(j+1)*NA-idx*NT*NU),NT*NU*NA)
            c = max(-S, cos_lo[idx]-err)
            acc += c*(lo if c>=0 else hi)
        if minimum is None or acc<minimum:
            minimum = acc
    # For u>=4, K(u) cosh(u/2) <= exp(u-exp(u)).
    # Its tail integral exp(-exp(4)) < 2^-64.
    bound = F(minimum, NU*S*S)-F(1,2**64)
    assert bound > F(1,1000), bound
    print("Uniform real-part integral over u >= 0 exceeds 1/1000.")
    print("Certified for |Re(s)-1/2| <= 1/2 and |Im(s)| <= 4.")
    print("All Jensen polynomials of degrees 1 through 16 are hyperbolic.")


if __name__=="__main__":
    main()
