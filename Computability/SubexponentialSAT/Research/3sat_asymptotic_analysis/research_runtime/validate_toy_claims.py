#!/usr/bin/env python3
"""Exact toy checks, NOT an implementation or proof of an improved SAT solver.
Uses only Python standard-library integer/Fraction arithmetic.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import comb
import json
from pathlib import Path
import argparse

def require(condition, message):
    if not condition:
        raise ValueError(message)

def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a)

def add(a, b):
    c = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return trim(c)

def scale(a, c):
    return trim([x * c for x in a])

def mul(a, b):
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return trim(c)

def ev(a, x):
    ans = Q(0)
    for c in reversed(a):
        ans = ans * x + c
    return ans

def affine_sub(a, t, alpha):
    out = (Q(0),)
    for c in reversed(a):
        out = add(mul(out, (Q(t), Q(alpha))), (c,))
    return out

def v2_int(x):
    x = abs(x)
    require(x, 'Exact check failed at original source line 43')
    return (x & -x).bit_length() - 1

def integral_at_two(x):
    return not x or v2_int(x.numerator) >= v2_int(x.denominator)
L = 4
a = 2
alpha = 8
nodes = list(range(-L, L))
den = Q(1)
for q in nodes:
    if q:
        den *= -q
W = {}
for x in range(L):
    for y in range(L):
        pol = (Q(1),)
        for q in nodes:
            if q != y - x:
                pol = mul(pol, (Q(-q), Q(1)))
        W[x, y] = scale(pol, 1 / den)
require(all((ev(W[x, y], 0) == int(x == y) for x in range(L) for y in range(L))), 'Exact check failed at original source line 60')
base_checks = 0
for t in nodes:
    for pol in W.values():
        require(all((integral_at_two(c) for c in affine_sub(pol, t, alpha))), 'Exact check failed at original source line 64')
        base_checks += 1
subsets = list(combinations(range(L), 2))
wedge = {}
max_degree = 0
for S in subsets:
    for T in subsets:
        p = add(mul(W[S[0], T[0]], W[S[1], T[1]]), scale(mul(W[S[0], T[1]], W[S[1], T[0]]), -1))
        require(ev(p, 0) == int(S == T), 'Exact check failed at original source line 74')
        require(len(p) - 1 <= 2 * (2 * L - 1), 'Exact check failed at original source line 75')
        max_degree = max(max_degree, len(p) - 1)
        wedge[S, T] = p
wedge_integral_checks = 0
locality_checks = 0
nonzero_local_entries = 0
for t in nodes:
    for (S, T), p in wedge.items():
        require(all((integral_at_two(c) for c in affine_sub(p, t, alpha))), 'Exact check failed at original source line 81')
        wedge_integral_checks += 1
        if t and v2_int(t) < a:
            i = v2_int(t)
            row_ones = sum((x >> i & 1 for x in S))
            col_ones = sum((1 - (y >> i & 1) for y in T))
            value = ev(p, t)
            if row_ones != col_ones:
                require(value == 0, 'Exact check failed at original source line 90')
            if value:
                nonzero_local_entries += 1
            locality_checks += 1
t = 4
table = [Q(0)] * (1 << t)
table[-1] = Q(1)
coeff = table[:]
for bit in range(t):
    for mask in range(1 << t):
        if mask & 1 << bit:
            coeff[mask] -= coeff[mask ^ 1 << bit]
require(coeff[-1] == 1 and sum((c != 0 for c in coeff)) == 1, 'Exact check failed at original source line 101')
binary_degree = max((mask.bit_count() for mask, c in enumerate(coeff) if c))
require(binary_degree == t, 'Exact check failed at original source line 103')
M = 128
D = 32
u = 16
k = M // D
Wmax = 4
shift = 6
p = M * D // u
weights = [b + shift for b in range(1, Wmax + 1) for _ in range(k)]
require(len(weights) == 16 and sum(weights) < p, 'Exact check failed at original source line 108')
counts = [0] * (1 << len(weights))
degrees = [0] * len(counts)
for mask in range(1, len(counts)):
    lsb = mask & -mask
    idx = lsb.bit_length() - 1
    prev = mask ^ lsb
    counts[mask] = counts[prev] + weights[idx]
    degrees[mask] = degrees[prev] + 1
    require(counts[mask] < p and degrees[mask] <= M, 'Exact check failed at original source line 114')
mode_result = {'M': M, 'D': D, 'u': u, 'multiplicity_per_weight': k, 'weights_before_shift': [1, Wmax], 'shift': shift, 'budget': p, 'catalogue_variables': len(weights), 'total_catalogue_weight': sum(weights), 'exhaustively_verified_binary_subsets': len(counts)}
lam = 1 << 60
eps = Q(1, 128 * 1024)
nu = 60
k_ratio = Q(1, nu)
depths = []
d = 0
while 8 ** (2 * d) < lam / k_ratio:
    ud = eps * lam // 2 ** d
    require(ud >= 1, 'Exact check failed at original source line 125')
    ratio_squared = Q(1, 8 ** d) * lam / ud
    root_squared = Q(lam, int(eps * lam))
    require(ratio_squared / root_squared == Q(1, 4 ** d), 'Exact check failed at original source line 128')
    depths.append({'depth': d, 'u': ud, 'squared_exponent_ratio_to_root': str(Q(1, 4 ** d))})
    d += 1
require(sum((Q(1, 2 ** d) for d in range(len(depths))), Q(0)) < 2, 'Exact check failed at original source line 131')
u_min = depths[-1]['u']
B = 10
precision_log_rhs = (B + 1) * 60 + u_min.bit_length()
require(u_min > precision_log_rhs, 'Exact check failed at original source line 135')
require(4 * eps < Q(1, 1000) and 48 * eps < Q(1, 1000), 'Exact check failed at original source line 137')
require(Q(98, 1000) * lam > 61, 'Exact check failed at original source line 138')
require(k_ratio >= Q(1, lam), 'Exact check failed at original source line 139')
result = {'status': 'all exact toy checks passed', 'scope': 'Local identities, integer budgets, and conditional recurrence only. No improved SAT algorithm, kernel compression, or recursive closure is validated.', 'cauchy': {'L': L, 'degree_bound': 2 * L - 1, 'identity_at_zero_entries': L * L, 'integral_substitution_checks': base_checks}, 'exterior_power': {'particle_number': 2, 'categorical_dimension': len(subsets), 'identity_at_zero_entries': len(wedge), 'degree_bound': 14, 'observed_max_degree': max_degree, 'integral_substitution_checks': wedge_integral_checks, 'group_occupancy_locality_checks': locality_checks, 'nonzero_local_entries': nonzero_local_entries}, 'binary_index_degree_counterexample': {'incidence_degree': 1, 'categorical_states': 1 << t, 'index_bits': t, 'boolean_index_degree': binary_degree}, 'mode_subset_test': mode_result, 'conditional_recurrence': {'lambda': lam, 'K_over_s': str(k_ratio), 'epsilon': str(eps), 'active_depths': depths, 'geometric_sum_less_than_two': True, 'precision_absorption_log2_lhs_u': u_min, 'precision_absorption_log2_rhs_bound': precision_log_rhs, 'precision_polynomial_power_tested': B}}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, help='Optionally save the JSON result to this path; stdout always contains the same JSON.')
args = parser.parse_args()
result['check_implementation'] = 'Explicit require calls remain active under python -O.'
rendered = json.dumps(result, indent=2) + '\n'
if args.output is not None:
    args.output.write_text(rendered)
print(rendered, end='')
