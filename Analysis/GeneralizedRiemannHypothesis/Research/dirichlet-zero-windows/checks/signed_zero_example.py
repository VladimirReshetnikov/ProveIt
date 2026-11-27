#!/usr/bin/env python3
"""Illustrate the signed explicit formula for the quartic character modulo 5.

Requires mpmath (tested with 1.3.0). Scans for sign changes, so the zero
list and sums are numerical illustrations, not certified enumerations.
"""
from functools import lru_cache
import mpmath as mp

mp.mp.dps = 27
chi = [0, 1, 1j, -1j, -1]  # Values in the residue-class order 0,1,2,3,4.
log2 = mp.log(2)
B = 3
step = mp.mpf(1) / 4
max_height = 100
epsilon = sum(chi[a] * mp.expj(2 * mp.pi * a / 5) for a in range(1,5)) / (1j * mp.sqrt(5))


@lru_cache(maxsize=None)
def hardy_z(t):
    s = mp.mpc(mp.mpf('0.5'), t)
    phase = mp.im(mp.loggamma((s + 1) / 2)) + (t * mp.log(5 / mp.pi) - mp.arg(epsilon)) / 2
    return mp.re(mp.expj(phase) * mp.dirichlet(s, chi))


def scan_ordinates():
    roots = []
    a = -mp.mpf(max_height)
    za = hardy_z(a)
    while a < max_height:
        b = a + step
        zb = hardy_z(b)
        if za == 0:
            roots.append(a)
        elif za * zb < 0:
            root = mp.findroot(hardy_z, (a, b), solver="anderson", tol=mp.mpf("1e-21"))
            if not a <= root <= b or abs(mp.dirichlet(mp.mpc("0.5", root), chi)) > mp.mpf("1e-16"):
                raise ArithmeticError("zero refinement failed")
            roots.append(root)
        a, za = b, zb
    return roots


def transform(t):
    # h(t) = int g(u) exp(i t u) du.  Translation leaves a real even envelope.
    def integrand(v):
        return mp.cos(2 * mp.pi * v)**4 * mp.sinc(B*v)**4 * mp.cos(t*v)
    envelope = 2 * mp.quad(integrand, [0, mp.mpf(1)/4])
    return mp.expj(t * log2) * envelope


def main():
    roots = scan_ordinates()
    sums = [(t, transform(t)) for t in roots]
    print('chi(2) = +i, p = 2, B = 3, fixed support log(2) +/- 1/4')
    print('negative and positive ordinates found with |gamma| < 10:')
    print(', '.join(mp.nstr(t, 15) for t in roots if abs(t) < 10))
    print('height   neg   pos   Im(sum_chi - sum_conjugate)     |difference from prime side|')
    prime_side = -2 * log2 / mp.sqrt(2)
    for cap in (10, 20, 40, 60, 80, 100):
        block = [(t,h) for t,h in sums if abs(t) <= cap]
        imag_diff = 2 * mp.fsum(mp.im(h) for t,h in block)
        neg = sum(t < 0 for t,h in block)
        print(f'{cap:6} {neg:5} {len(block)-neg:5}   {float(imag_diff): .12f}                   {float(abs(imag_diff-prime_side)):.6g}')
    print(f'exact full imaginary difference = -sqrt(2) log(2) = {float(prime_side):.12f}')


if __name__ == '__main__':
    main()
