r"""Is a LOGARITHM-based certificate cheaper than the enclosure-of-theta certificate?

The committed FiniteCheck32768 certifies m^theta not in Z by trapping theta between two
rationals Lp/Lq < theta < Up/Uq and comparing a^Lq < m^Lp -- integers of ~1.5e8 bits.

The alternative, which Theorem thm:finite-range already uses in software: certify
    log a * log 2  <  log 3 * log m  <  log(a+1) * log 2
directly, from rational enclosures of the four logarithms. The decisive gap is

    log 3 log m - log 2 log a = log 2 * log(1 + delta/a)  ~  log2 * delta / a,

so the precision needed is only about log2(a/delta) bits. This script measures that gap on
the real data and extrapolates.
"""
from decimal import Decimal, getcontext
import math
import re

getcontext().prec = 120
L2 = Decimal(2).ln()
L3 = Decimal(3).ln()
TH = L3 / L2

LEAN = ("C:/ProveIt/Analysis/ExponentialIdentities/Lean/ExponentialIdentities/"
        "TwoBaseIntegerExponent/")
s = open(LEAN + "FiniteCheck32768.lean", encoding="utf-8").read()
rows = []
for c in range(4):
    b = re.search(rf"certTable32768_{c} : List \(\u2115 \u00d7 \u2115\) := \[(.*?)\n\]", s, re.S).group(1)
    rows += [int(a) for a, _e in re.findall(r"\((\d+), (\d+)\)", b)]

print("measuring the decisive gap  |log3*log m - log2*log a|  over [16384, 32768)")
worst = None
for i, a in enumerate(rows):
    m = 16384 + i
    if m == 16384:
        continue
    lm, la = Decimal(m).ln(), Decimal(a).ln()
    gap_lo = L3 * lm - L2 * la               # > 0
    gap_hi = L2 * Decimal(a + 1).ln() - L3 * lm   # > 0
    g = min(gap_lo, gap_hi)
    if worst is None or g < worst[0]:
        worst = (g, m, a)
g, m, a = worst
print(f"  worst gap {float(g):.4e} at m={m}, a={a}")
print(f"  bits of precision needed there: {float(-Decimal(g).ln()/Decimal(2).ln()):.1f}")
print(f"  (theorem thm:finite-range reports 6.26e-13 as its smallest endpoint at A<=100000)")

print()
print("extrapolation: worst gap ~ log2 * delta_min / a, with a ~ N^theta, delta_min ~ 1/N")
print(f"{'N':>10} {'a~N^theta':>12} {'gap':>12} {'bits':>7} {'rows':>12}")
for k in (15, 20, 24, 27, 30, 40):
    N = Decimal(2) ** k
    a_typ = N ** TH
    gap = L2 / (N * a_typ)
    bits = float(-(gap.ln()) / Decimal(2).ln())
    print(f"2^{k:<8} {float(a_typ):12.3g} {float(gap):12.3e} {bits:7.0f} {float(N):12.3g}")

print()
print("compare: the enclosure-of-theta certificate at N=2^15 forms integers of")
print("  10444047 * log2(26983) = 1.54e8 bits, and scales like N^((1+theta)/2).")
