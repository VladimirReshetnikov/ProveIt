#!/usr/bin/env python3
"""Rational all-orders large-k coefficients for r_k / P_k(0)."""
from fractions import Fraction as F
from math import factorial
from verify_sign import mul, coefficients
import json
from pathlib import Path


def correction_coefficients(order):
    n = 2*order
    h, _, _, b = coefficients(n)
    q = [F(0)]*(n+1)
    for j in range(n//2+1):
        q[2*j] = F(1, 4**j*factorial(2*j+1))
    v = [F(0)]+q[:n]
    s = [F(1)]+[F(0)]*n
    p = s.copy()
    for j in range(1, n+1):
        p = mul(p, v, n)
        for k in range(j, n+1):
            s[k] -= b[j]*p[k]
    a = []
    for k in range(n+1):
        a.append(h[k]-sum(s[i]*a[k-i] for i in range(1, k+1)))
    u = q.copy()
    u[0] = 0
    powers = [[F(1)]+[F(0)]*n]
    for j in range(1, order+1):
        powers.append(mul(powers[-1], u, n))
    a_powers = [mul(a, p, n) for p in powers]
    c = [F(1)]+[F(0)]*order
    polys = []
    for m in range(1, n+1):
        # C_m(k)=[t^m] A(t)q(t)^(k-m), a polynomial in k.
        cm = [F(0)]*(m//2+1)
        binomial = [F(1)]
        for ell in range(m//2+1):
            if ell:
                binomial = [z/ell for z in mul(
                    binomial, [F(-m-ell+1), F(1)], ell)]
            for degree, cc in enumerate(binomial):
                cm[degree] += cc*a_powers[ell][m]
        polys.append([str(z) for z in cm])
        # b_(k-m)/b_k = 4^m x^m B_m(x), x=1/k.
        bm = [F(1)]+[F(0)]*order
        for j in range(m):
            bm = mul(bm, [F(1), F(-j)], order)
            for lam in [F(2*j+3, 2), F(2*j-1, 2)]:
                bm = mul(bm, [lam**i for i in range(order+1)], order)
        for degree, cc in enumerate(cm):
            start = m-degree
            for i in range(max(0, order-start+1)):
                c[start+i] += 4**m*cc*bm[i]
    return c, polys


def main():
    c, polys = correction_coefficients(8)
    assert c[:3] == [F(1), F(-1, 3), F(-11, 18)]
    data = {
        "meaning": "r_k/P_k(0) ~ sum c_j/k^j as k tends to infinity",
        "c": [str(z) for z in c],
        "C_m_polynomials_ascending_powers_of_k": polys,
    }
    path = Path(__file__).with_name("large_order_coefficients.json")
    path.write_text(json.dumps(data, indent=2)+"\n")
    print("c_0,...,c_8 =", ", ".join(map(str, c)))
    print("Saved:", path)


if __name__ == "__main__":
    main()
