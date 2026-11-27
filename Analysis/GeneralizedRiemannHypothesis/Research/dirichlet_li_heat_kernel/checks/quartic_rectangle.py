#!/usr/bin/env python3
"""Count all mod-five quartic L-zeros in a low rectangle by the argument principle.

Run beside quartic_echo.py with Python 3 and mpmath 1.3.0. All input endpoints
are rational. Each accepted contour segment maps to a rectangle excluding zero.
The crossing count of the polygon of actual endpoint values is then exact.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, prod

from mpmath import iv
from quartic_echo import BERNOULLI, ball, log_int


def lbox(start, end):
    def interval(a, b):
        return iv.mpf([ball(min(a, b)).a, ball(max(a, b)).b])
    s = iv.mpc(interval(start[0], end[0]), interval(start[1], end[1]))
    assert abs(s) < 5 and s.real >= ball(F(-1, 99))
    n, m = 12, 8
    poch = [iv.mpc(1)]
    for j in range(m-1):
        poch.append(poch[-1] * (s + j))
    total = iv.mpc(0)
    for a, weight in enumerate((1, -iv.j, iv.j, -1), 1):
        z = 5*n + a
        tail = z / (5 * (s-1)) + iv.mpf("0.5")
        for k, b in enumerate(BERNOULLI[:4], 1):
            tail += ball(b)*poch[2*k-1]*(iv.mpf(5)/z)**(2*k-1)/factorial(2*k)
        total += weight * (sum(iv.exp(-s*log_int(5*j+a)) for j in range(n))
                           + iv.exp(-s*log_int(z))*tail)
    # Uniform EM remainder at Re(s)>=-1/99. The rational lower bound for
    # |Re(s)+m-1| is m-1-1/99.
    e = ball(F(m-1)-F(1,99))
    rem = (4*ball(abs(BERNOULLI[3]))*prod(range(5,5+m))*5**(m-1)
           / factorial(m) / e * iv.mpf(5*n)**(-e))
    err = iv.mpf([-1, 1])*rem
    return total + iv.mpc(err, err)


@lru_cache(maxsize=None)
def sign_at(pt):
    h = lbox(pt, pt).imag
    if h > 0:
        return 1
    if h < 0:
        return -1
    raise RuntimeError("An endpoint is too close to the counting ray")


def winding_number():
    left, right, height = F(-1,100), F(101,100), F("4.14")
    corners = ((left,-height), (right,-height), (right,height), (left,height))
    w, count = 0, 0
    stack = list(zip(corners, corners[1:]+corners[:1]))
    while stack:
        x, y = stack.pop()
        v = lbox(x,y)
        if v.imag > 0 or v.imag < 0 or v.real < 0:
            count += 1
        elif v.real > 0:
            w += (sign_at(y)-sign_at(x))//2
            count += 1
        else:
            if max(abs(x[k]-y[k]) for k in range(2)) < F(1,10**8):
                raise RuntimeError("Cannot exclude a contour zero")
            z = tuple((a+b)/2 for a,b in zip(x,y))
            stack.extend(((x,z), (z,y)))
    return w,count


if __name__ == '__main__':
    w,count = winding_number()
    assert w == 1
    print(f"Contour image certified by {count} rectangles excluding zero.")
    print(f"Counterclockwise winding number: {w}.")
    print("All zeros counted with multiplicity in -0.01 < Re(s) < 1.01,")
    print("|Im(s)| < 4.14: precisely one. There are no contour zeros.")
