#!/usr/bin/env python3
"""Exact residue-field test at a conductor from the parameter family."""
from math import gcd, isqrt
from check_vacuum_frames import factor, local_frame


def prime(n):
    return n >= 2 and all(n % i for i in range(2, isqrt(n) + 1))


def geometric_sum(x, count, ell):
    if x == 1:
        return count % ell
    return (pow(x, count, ell) - 1) * pow(x - 1, -1, ell) % ell


def check():
    q0, d = 18480, 9239
    q, n = q0 * 3**5, (d + 1)//4
    assert prime(d) and d % q0 == q0//2 - 1
    # ell splits K and contains a primitive q-th root; verify the supplied data.
    ell, root, sqrt_minus_d = 76340881, 12104500, 23060863
    assert prime(ell) and (sqrt_minus_d**2+d) % ell == 0
    factors = factor(q)
    assert pow(root, q, ell) == 1
    assert all(pow(root, q//p, ell) != 1 for p in factors)
    beta = (1+sqrt_minus_d)*pow(2, -1, ell) % ell
    rows = sorted(set([i for i in range(1, 90) if gcd(i, q) == 1] +
                      [q-1, q-13, q//2+1]))
    assert all(gcd(s, q) == 1 for s in rows)
    h_total, comparisons = 0, 0
    for p, a in factors.items():
        P, A, B, L, h = local_frame(q, p, a, n, True)
        h_total += h
        z = pow(root, q//p, ell)
        def eval_pair(pair, scalar):
            return (pair[0]+scalar*pair[1])*pow(P,-1,ell) % ell
        A0, B0 = (eval_pair(X, beta) for X in (A,B))
        A1, B1 = (eval_pair(X, 1-beta) for X in (A,B))
        for s in rows:
            for t in rows:
                inner = L + sum((A0*pow(z, s*k, ell)+B0) *
                                (A1*pow(z, -t*k, ell)+B1)
                                for k in range(1,p))
                phase = geometric_sum(pow(root, s-t, ell), q//p, ell)
                assert (phase*inner - (h if s == t else 0)) % ell == 0
                comparisons += 1
        print(f"p={p:2d}  P={P:3d}  H_p={h}  residue={h % p}")
    assert gcd(h_total, q) == 1 and h_total <= 4*q**5*(1+n)**2
    print(f"q0={q0}, tower exponent=0, q={q}, d={d}, n={n}, H={h_total}")
    print(f"Tested {comparisons} individual block entries modulo {ell} "
          f"on {len(rows)} distinct character rows; gcd(H,q)=1.")


if __name__ == "__main__":
    check()
