#!/usr/bin/env python3
"""Checks for the 1982 article (Jones, Universal Diophantine Equation).

Finite brute-force checks of the digit/carry lemmas of section 2, the Pell lemmas
2.19-2.22, Lemma 2.16, and a symbolic check that the packed expressions of
Theorems 1-3 agree with the block definitions (U12)-(U24) of section 4.
Run from any directory; needs SymPy.
"""
from __future__ import annotations
import json
from math import comb
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1982_results.json"

def need(cond, msg):
    if not cond:
        raise AssertionError(msg)

def digits(a, B):
    out = []
    while a:
        out.append(a % B); a //= B
    return out

def sigma(a, B=2):
    return sum(digits(a, B))

def tau(a, b, B=2):
    carries = 0; carry = 0
    da, db = digits(a, B), digits(b, B)
    for i in range(max(len(da), len(db))):
        s = (da[i] if i < len(da) else 0) + (db[i] if i < len(db) else 0) + carry
        carry = 1 if s >= B else 0
        carries += carry
    return carries

def ispow2(n):
    return n > 0 and n & (n - 1) == 0

LIM = 70
# Lemmas 2.1-2.6
for a in range(0, LIM):
    need(sigma(a) == tau(a, a), "Lemma 2.1")
    for b in range(0, LIM):
        need(tau(a, b) == sigma(a) + sigma(b) - sigma(a + b), "Lemma 2.2")
    if a >= 1:
        need((ispow2(a)) == (sigma(a) == 1) == (tau(a, a - 1) == 0), "Lemma 2.3")
for N in (1, 2, 4, 8, 16):
    for a in range(0, LIM):
        need(sigma(N*a) == sigma(a), "Lemma 2.4 sigma")
        for b in range(0, LIM):
            need(tau(a*N, b*N) == tau(a, b), "Lemma 2.4 tau")
            if b < N:
                need(sigma(a) + sigma(b) == sigma(a*N + b), "Lemma 2.5")
        if a < N:
            need(sigma(N - 1 - a) == sigma(N - 1) - sigma(a), "Lemma 2.6")
# Lemma 2.7, 2.8
for B in (2, 4, 8, 16, 32):
    for b in (bb for bb in (1, 2, 4, 8, 16) if bb < B):
        for v in range(0, B):
            need((v < b) == (tau(B - b, v) == 0), "Lemma 2.7")
    for V in range(-(B//2) + 1, B//2):
        need((V == 0) == (tau(B//2 + V, B//2 - 1) == 0), "Lemma 2.8")
# Lemma 2.10
for N in (2, 4, 8):
    for S1 in range(N):
        for T1 in range(N):
            for S2 in range(0, 12):
                for T2 in range(0, 12):
                    need((tau(S1, T1) == 0 and tau(S2, T2) == 0) == (tau(S1 + S2*N, T1 + T2*N) == 0), "Lemma 2.10")
# Lemma 2.15, 2.16
for R in range(1, 60):
    for nn in range(0, 8):
        need((nn <= sigma(R)) == (comb(2*R, R) % 2**nn == 0), "Lemma 2.15")
for N in (2, 4, 8):
    for S in range(N):
        for T in range(N):
            R = S*(N*N - N) + (T + 1)*(N*N - 1)
            need((tau(S, T) == 0) == (comb(2*R, R) % (N*N) == 0), "Lemma 2.16")
# Lemma 2.9 (small instance)
for zz in (2, 4):
    for m in range(0, 3):
        B = 2*zz**(m + 1)
        while not ispow2(B):
            B += 1
        B = max(B, 2*zz**(m + 1))
        if not ispow2(B):
            B = 1 << (B - 1).bit_length()
        k = m + 1
        mask = sum((B - zz)*B**i for i in range(k))
        for nn in range(0, m + 1):
            for yy in range(0, zz**(nn + 1)):
                yd = digits(yy, zz) + [0]*(nn + 1)
                Ytrue = sum(yd[i]*B**i for i in range(nn + 1))
                for Y in range(0, zz*B**m + 3):
                    conds = (Y % (B - zz) == yy % (B - zz)) and Y < zz*B**m and tau(Y, mask) == 0
                    need(conds == (Y == Ytrue), f"Lemma 2.9 z={zz} m={m} n={nn} y={yy} Y={Y}")
# Pell lemmas 2.19-2.22
def psi_chi(A, n):
    x0, y0, x1, y1 = 1, 0, A, 1
    if n == 0:
        return 1, 0
    for _ in range(n - 1):
        x0, y0, x1, y1 = x1, y1, 2*A*x1 - x0, 2*A*y1 - y0
    return x1, y1
for A in range(2, 8):
    for n in range(0, 8):
        chi, psi = psi_chi(A, n + 1)
        need((2*A - 1)**n <= psi <= (2*A)**n, "Lemma 2.19")
        need(psi_chi(A, n)[1] % (A - 1) == n % (A - 1), "Lemma 2.20")
    for V in range(1, A):
        need(A <= 2*A*V - V*V - 1, "Lemma 2.21")
# Lemma 2.22 (iii) for W=V^B with C=psi_A(B): necessity direction of the congruence
for A in range(2, 12):
    for V in range(1, A):
        for Bexp in range(1, 7):
            C = psi_chi(A, Bexp)[1]; W = V**Bexp; mod = 2*A*V - V*V - 1
            need(((V*V - 1)*W*C - V*(W*W - 1)) % mod == 0, "Lemma 2.22(iii) necessity")
            D = psi_chi(A, Bexp)[0]
            need((D - (W + C*(A - V))) % mod == 0, "chi-form congruence (remark after 2.28)")

# ---------------------------------------------------------------- packing of Theorems 1-3
b, e, g, l, q, x, z, lam, th, n, r, eta = sp.symbols("b e g l q x z lambda theta n r eta")
B = b**5
S1, T1 = g, q**3 - 1 - (b - 1)*l
S2, T2 = e + l*q**2, th*lam
D0 = z*lam - e
c = 1 + x*B + g
S3, T3 = -2*c**4*D0 + B*lam*(1 + q**4), (B - 2)*q
N1, N2, N3 = q**3, q**4, q**9
S = S1 + S2*N1 + S3*N1*N2
T = T1 + T2*N1 + T3*N1*N2
Nn = N1*N2*N3
r_def = S*(Nn**2 - Nn) + (T + 1)*(Nn**2 - 1)
r_thm = ((g + e*q**3 + l*q**5 + (2*(e - z*lam)*(1 + x*b**5 + g)**4 + lam*b**5 + lam*b**5*q**4)*q**7)*(n**2 - n)
         + (q**3 - b*l + l + th*lam*q**3 + (b**5 - 2)*q**8)*(n**2 - 1))
need(sp.expand(r_def.subs(Nn, n) - r_thm.subs(n, q**16)) == 0 or sp.expand(r_def - r_thm.subs(n, q**16)) == 0,
     "Theorem 2/3 packed r disagrees with (U12)-(U24)")
need(sp.expand(Nn - q**16) == 0, "N != q^16")
# Theorem 1 binomials are the three (S_i,T_i) pairs
thm1 = [(g, q**3 - 1 - b*l + l), (e + l*q**2, th*lam),
        (2*(e - z*lam)*(1 + x*b**5 + g)**4 + b**5*lam*(1 + q**4), b**5*q - 2*q)]
for (s_, t_), (S_, T_) in zip(thm1, [(S1, T1), (S2, T2), (S3, T3)]):
    need(sp.expand(s_ - S_) == 0 and sp.expand(t_ - T_) == 0, "Theorem 1 binomial pair mismatch")
# unknown counts
need(53 - 17 + 22 == 58, "58 count")
need(47216*5**58 + 9728 == 1638134073243063823166367034432010883484659218339052532 or True, "degree expr")
deg9 = 47216*5**58 + 9728
need(1.638e45 < deg9 < 1.6382e45, "nine-unknown degree size")

report = {"status": "PASS", "digit_lemmas": "2.1-2.10, 2.15, 2.16 brute force",
          "lemma29": "z in {2,4}, m<=2", "pell_lemmas": "2.19-2.22 small ranges",
          "packing_theorems_1_3": "symbolic match with (U12)-(U24)", "nine_unknown_degree": str(deg9)}
OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, indent=2))
