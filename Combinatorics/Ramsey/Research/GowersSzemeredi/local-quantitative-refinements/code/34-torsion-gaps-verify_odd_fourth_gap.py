#!/usr/bin/env python3
"""Exact certificates for the fourth Gowers norm gap; standard library only."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from decimal import Decimal, getcontext
import argparse
import json
from pathlib import Path

V4 = [tuple((i >> j) & 1 for j in range(4)) for i in range(16)]
counts = Counter()
for mask in range(1 << 15):
    chosen = [V4[i + 1] for i in range(15) if (mask >> i) & 1]
    if all(sum(v[j] for v in chosen) == 4 for j in range(4)):
        counts[len(chosen)] += 1
assert dict(counts) == {5: 1, 6: 27, 7: 111, 8: 111, 9: 27, 10: 1}

p = F(49, 50)
lo_K = F(193, 100)
deltas = {
    "p_fourth_root_above_99_over_100": p - F(99,100)**4,
    "K_lower": F(222,16) - lo_K**4,
    "target_fourth_root_below_47_over_50": F(47,50)**4-F(150,193),
    "low_pair_mass_case":
        F(35,8)*(1+12*p*(1-p)+6*p*p*(1-p)*(1-p))-F(81,16),
    "high_pair_mass_case": F(35,8)+F(7,244)*p**4*F(111,20)**2-F(81,16),
    "order_three_case": lo_K*p-F(3,2),
}
assert all(delta > 0 for delta in deltas.values())
assert 2*factorial(8)//(factorial(5)*factorial(2)) == 336
assert 2*factorial(8)//factorial(6) == 112
assert F(27**2,21)+F(1,7) == F(244,7)

# The signed pairs involved in the retained monomials stay distinct.
for order in range(5,102,2):
    first = {1 % order,(-1) % order}
    third = {3 % order,(-3) % order}
    fifth = {5 % order,(-5) % order}
    assert first.isdisjoint(third)
    if order != 5:
        assert first.isdisjoint(fifth) and third.isdisjoint(fifth)

# Exact checks establishing the crossing/diffuse branches in d=4,...,8.
higher = {}
for d in range(4, 10):
    m = 2**(d-2)
    C = F(comb(2*m,m), 2**m)
    K_power_m = F(222,16)**(m//4)
    pure_gap = K_power_m-C
    diffuse_gap = C*(m-F(m-1,2**(m-1)))-K_power_m
    assert (pure_gap > 0) == (d <= 8)
    if d <= 8:
        assert diffuse_gap > 0
    higher[str(d)] = {
        "m": m,
        "pure_pair_moment_below_dual_endpoint": pure_gap > 0,
        "diffuse_case_above_dual_endpoint": diffuse_gap > 0,
    }

# Rational identity for the two equivalent dominant-pair profiles.
for m in range(1, 17):
    for numerator in range(11):
        p_test = F(numerator,10)
        q_test = 1-p_test
        H_first = sum(F(comb(m,k)**2)*p_test**k*q_test**(m-k)
                      for k in range(m+1))
        H_second = sum(F(comb(m,2*j)*comb(2*j,j))*(p_test*q_test)**j
                       for j in range(m//2+1))
        assert H_first == H_second

V3 = [tuple((i >> j) & 1 for j in range(3)) for i in range(8)]
face = defaultdict(lambda: [0]*9)
for a in product((-3,-1,1,3), repeat=8):
    if sum(a):
        continue
    moments = tuple(sum(a[i]*V3[i][j] for i in range(8)) for j in range(3))
    face[moments][sum(abs(x)==3 for x in a)] += 1
P = [0]*17
for moments, a in face.items():
    b = face[tuple(-x for x in moments)]
    for i, v in enumerate(a):
        for j, w in enumerate(b):
            P[i+j] += v*w
expected = [222,864,4080,9120,25640,31808,55120,49280,52360,
            28320,24160,4256,5920,0,0,0,222]
assert P == expected
N = sum(coef*(-1)**i*7**(16-i) for i,coef in enumerate(P))
assert N == 5465198316262956

# Independent exact order-three single-pair Fourier enumeration.
face3 = defaultdict(lambda: [0]*9)
for a in product((-1,1), repeat=8):
    if sum(a) % 3:
        continue
    moments = tuple(sum(a[i]*V3[i][j] for i in range(8)) % 3 for j in range(3))
    face3[moments][sum(x == 1 for x in a)] += 1
phase_counts = [0]*17
for moments, a in face3.items():
    b = face3[tuple((-x)%3 for x in moments)]
    for i, v in enumerate(a):
        for j, w in enumerate(b):
            phase_counts[i+j] += v*w
phase_coeffs = {str(2*k-16): value for k,value in enumerate(phase_counts) if value}
assert phase_coeffs == {"-12":8,"-6":16,"0":286,"6":16,"12":8}

report = {
    "dual_subset_counts": dict(sorted(counts.items())),
    "rational_certificate_positive_differences": {k:str(v) for k,v in deltas.items()},
    "two_harmonic_polynomial_coefficients_ascending": P,
    "scaled_two_harmonic_value_at_minus_one_seventh": N,
    "lower_bound_c4_fourth_power": str(F(4804**4,N)),
    "new_rational_upper_bound": "2/3",
    "resonance_counts": {"third_harmonic":336,"fifth_harmonic":112},
    "resonance_cauchy_factor": "244/7",
    "higher_dimensional_crossing_checks": higher,
    "order_three_phase_fourier_coefficients": phase_coeffs,
}
getcontext().prec=60
report["lower_bound_c4_decimal"] = str(Decimal(4804)/Decimal(N).sqrt().sqrt())
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument(
    "--output", type=Path,
    default=Path(__file__).resolve().parents[1] / "data" / "odd_fourth_gap_certificates.json",
    help="JSON output path; default is the package data directory, independent of cwd.",
)
output = parser.parse_args().output
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
print(f"Certificate written to {output.resolve()}")
