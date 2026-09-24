#!/usr/bin/env python3
"""Checks for the 1976 article (Jones, Sato, Wada, Wiens).

Exact and finite checks only. Run from any directory; needs SymPy.
"""
from __future__ import annotations
import json, random, sys
from math import factorial, isqrt
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1976_results.json"

def need(cond, msg):
    if not cond:
        raise AssertionError(msg)

# ---------------------------------------------------------------- Theorem 1 polynomial
syms = sp.symbols("a b c d e f g h i j k l m n o p q r s t u v w x y z")
a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z = syms
brackets = [
    w*z + h + j - q,
    (g*k + 2*g + k + 1)*(h + j) + h - z,
    2*n + p + q + z - e,
    16*(k + 1)**3*(k + 2)*(n + 1)**2 + 1 - f**2,
    e**3*(e + 2)*(a + 1)**2 + 1 - o**2,
    (a**2 - 1)*y**2 + 1 - x**2,
    16*r**2*y**4*(a**2 - 1) + 1 - u**2,
    ((a + u**2*(u**2 - a))**2 - 1)*(n + 4*d*y)**2 + 1 - (x + c*u)**2,
    n + l + v - y,
    (a**2 - 1)*l**2 + 1 - m**2,
    a*i + k + 1 - l - i,
    p + l*(a - n - 1) + b*(2*a*n + 2*a - n**2 - 2*n - 2) - m,
    q + y*(a - p - 1) + s*(2*a*p + 2*a - p**2 - 2*p - 2) - x,
    z + p*l*(a - p) + t*(2*a*p - p**2 - 1) - p*m,
]
P = (k + 2)*(1 - sum(B**2 for B in brackets))
poly = sp.Poly(P, *syms)
need(poly.total_degree() == 25, "degree of (1) is not 25")
need(len(P.free_symbols) == 26, "(1) does not have 26 variables")

# The published example value -76 (introduction). Witness found by search.
witness = dict(a=0, b=0, c=0, d=0, e=1, f=6, g=0, h=2, i=1, j=0, k=0, l=0, m=1,
               n=0, o=2, p=1, q=0, r=0, s=0, t=0, u=1, v=0, w=0, x=1, y=0, z=4)
val = P.subs({sp.Symbol(kk): vv for kk, vv in witness.items()})
need(val == -76, f"witness does not give -76 (got {val})")

# ---------------------------------------------------------------- formula (5) for p_n
def rem(yy, xx):  # r(y,0)=y convention of the article
    return yy if xx == 0 else yy % xx

def pd(uu, vv):  # proper subtraction
    return max(uu - vv, 0)

def p_formula(nn):
    return sum(pd(1, pd(sum(rem(factorial(pd(jj, 1))**2, jj) for jj in range(0, ii + 1)), nn))
               for ii in range(0, nn*nn + 1))

need(all(p_formula(nn) == sp.prime(nn) for nn in range(1, 41)), "formula (5) fails")

# ---------------------------------------------------------------- Lemma 2.3 lower bound
lemma23 = []
for E in range(2, 7):
    D = E**3*(E + 2); nn = 0
    while True:
        val = D*(nn + 1)**2 + 1
        if isqrt(val)**2 == val:
            break
        nn += 1
    bound = E - 1 + E**(E - 2)
    need(nn >= bound, f"Lemma 2.3 bound fails at e={E}")
    lemma23.append({"e": E, "least_n": nn, "bound": bound})

# ---------------------------------------------------------------- Lemma 2.4 congruence
def chi_psi(A, N):
    x0, y0, x1, y1 = 1, 0, A, 1
    if N == 0:
        return 1, 0
    for _ in range(N - 1):
        x0, y0, x1, y1 = x1, y1, 2*A*x1 - x0, 2*A*y1 - y0
    return x1, y1

for A in range(1, 9):
    for pp in range(0, 12):
        for N in range(0, 9):
            X, Y = chi_psi(A, N); mod = 2*A*pp - pp*pp - 1
            rhs = pp**N + Y*(A - pp)
            if mod == 0:
                need(X == 1, "Lemma 2.4 degenerate case")
            else:
                need((X - rhs) % mod == 0, f"Lemma 2.4 congruence fails a={A} p={pp} n={N}")
            if 0 < pp**N < A:
                need(rhs <= X, f"Lemma 2.4 inequality fails a={A} p={pp} n={N}")

# ---------------------------------------------------------------- Lemma 2.10
for K in range(1, 5):
    for N in ((2*K)**K, (2*K)**K + 1, (2*K)**K + 7):
        for PP in (N**K + 1, N**K + 5, 2*N**K):
            R = (PP + 1)**N % PP**(K + 1)
            need(R != 0, "Lemma 2.10 remainder zero")
            val = sp.Rational((N + 1)**K*PP**K, R)
            need(factorial(K) < val < factorial(K) + 1, f"Lemma 2.10 fails k={K} n={N} p={PP}")

# ---------------------------------------------------------------- Theorem 2.12 <-> (1)
# Replace k by k+1 in the fourteen equations of Theorem 2.12, move everything to one
# side, and compare the resulting sum of squares with the bracket sum of (1).
eqs = [
    q - (w*z + h + j),
    z - ((g*k + g + k)*(h + j) + h),
    (2*k)**3*(2*k + 2)*(n + 1)**2 + 1 - f**2,
    e - (p + q + z + 2*n),
    e**3*(e + 2)*(a + 1)**2 + 1 - o**2,
    x**2 - ((a**2 - 1)*y**2 + 1),
    u**2 - (16*(a**2 - 1)*r**2*y**4 + 1),
    (x + c*u)**2 - (((a + u**2*(u**2 - a))**2 - 1)*(n + 4*d*y)**2 + 1),
    m**2 - ((a**2 - 1)*l**2 + 1),
    l - (k + i*(a - 1)),
    n + l + v - y,
    m - (p + l*(a - n - 1) + b*(2*a*(n + 1) - (n + 1)**2 - 1)),
    x - (q + y*(a - p - 1) + s*(2*a*(p + 1) - (p + 1)**2 - 1)),
    p*m - (z + p*l*(a - p) + t*(2*a*p - p**2 - 1)),
]
S212 = sum(E.subs(k, k + 1)**2 for E in eqs)
need(sp.expand(S212 - sum(B**2 for B in brackets)) == 0, "Theorem 2.12 shifted by k+1 does not give (1)")

report = {"status": "PASS", "degree": 25, "variables": 26, "minus76_witness": witness,
          "formula5_checked": "n=1..40", "lemma23": lemma23,
          "lemma24": "a=1..8, p=0..11, n=0..8", "lemma210": "k=1..4 samples",
          "theorem212_equals_(1)": True}
OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, indent=2))
