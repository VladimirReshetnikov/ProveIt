"""Numeric audit of the impossibility chain of Theorem A.

  (1)  P = N                        (Abel + balance B0)
  (2)  Phi^+_tot <= 4 P             (coefficients are recovered from tails)
  (3)  N <= 2 Z (m+j*) lnA Phi^+ /A (per-prime rescue + divisor counting + Huxley)
  =>   N <= 8 Z (m+j*) lnA N / A  =>  N = 0  whenever  A > 8 Z (m+j*) ln A.
"""
import random
from fractions import Fraction
from math import log

random.seed(3)

def audit(M, A, J, S, B, trials):
    """random balanced-ish arrays: check (1) and (2) exactly."""
    worst = Fraction(0)
    bad1 = 0
    for _ in range(trials):
        # random support: slice j has levels idx[j]
        c = {}
        idx = {}
        for j in range(J):
            s = random.randint(1, S)
            idx[j] = sorted(random.sample(range(0, S + 2), s))
            for i in idx[j]:
                c[(i, j)] = random.randint(-B, B)
        # force B0 exactly by adjusting one weight-1 cell if present, else skip test (1)
        Pmass = 0; Nmass = 0
        bal = sum(c[(i, j)] * M**i * A**j for (i, j) in c)
        for j in range(J):
            T = {}
            row = idx[j]
            for k in range(len(row)):
                T[k] = sum(c[(row[l], j)] for l in range(k, len(row)))
            prev = 0
            for k in range(len(row)):
                d = M**row[k] - prev; prev = M**row[k]
                t = T[k] * d * A**j
                if t > 0: Pmass += t
                else: Nmass += -t
        if Pmass - Nmass != bal:
            bad1 += 1
        # (2) Phi^+ <= 4 P holds whenever the array is balanced (P = N); check the
        #     general inequality Phi^+ <= 2P + 2N which is what the proof uses.
        phip = sum(c[(i, j)] * M**i * A**j for (i, j) in c if c[(i, j)] > 0)
        if 2 * Pmass + 2 * Nmass > 0:
            r = Fraction(phip, 2 * Pmass + 2 * Nmass)
            worst = max(worst, r)
    return bad1, worst

for (M, A, J, S, B) in [(5, 11, 3, 4, 6), (2, 3, 3, 4, 5), (16390, 4782971, 3, 3, 7)]:
    bad1, worst = audit(M, A, J, S, B, 3000)
    print(f"M={M} A={A}: (1) 'P - N = balance' failures over 3000 random arrays = {bad1};"
          f"  (2) worst Phi^+/(2P+2N) = {float(worst):.4f}  (proof needs <= 1)")

print()
print("=== size condition at the corpus scale ===")
x = 14
M = 2**x + 6; A = 3**x + 2
lnA = log(A)
for (Z, mj) in [(7, 7), (20, 10), (100, 20), (500, 50), (5000, 100)]:
    thr = 8 * Z * mj * lnA
    print(f"  |S|=Z={Z:5d}, m+j*={mj:4d}:  8 Z (m+j*) lnA = {thr:14.1f}   A = {A}"
          f"   condition A > threshold: {A > thr}")
print()
print("=== control instantiation (M,A)=(2^m,3^m) ===")
for mm in [14, 20, 30]:
    Mc, Ac = 2**mm, 3**mm
    print(f"  m={mm}: A={Ac}, 8*7*7*lnA = {8*7*7*log(Ac):.1f} -> hypotheses of Theorem A"
          f" hold for controls too: {Ac > 8*7*7*log(Ac)}")
