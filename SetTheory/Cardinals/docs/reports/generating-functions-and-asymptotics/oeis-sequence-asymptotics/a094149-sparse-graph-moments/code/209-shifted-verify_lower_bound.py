"""Independent finite verification of the shifted-Bell lower bound.
All code authored locally. Exhaustive walk DFS is independent of the proof's
partition/composition construction and of the Bauer--Golinelli recurrence.
Finite checks audit the identification and formulas, not their all-k proof.
"""
from collections import Counter, deque
from math import comb
from pathlib import Path
import json

import argparse
CHECKS = 0
def require(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise RuntimeError(str(message))

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--self-test-failure', action='store_true')
args = parser.parse_args()
if args.self_test_failure:
    require(False, 'intentional failure: explicit checks remain active')

OUT = Path(__file__).parent / 'data'
OUT.mkdir(exist_ok=True)
N = 16
S = [[0] * (N + 2) for _ in range(N + 2)]
S[0][0] = 1
for k in range(1, N + 2):
    for l in range(1, k + 1):
        S[k][l] = S[k - 1][l - 1] + l * S[k - 1][l]
B = [sum(r) for r in S]
F = [0, 1]
for _ in range(2 * N + 1):
    F.append(F[-1] + F[-2])

def norm(v):
    d = {}
    return tuple((d.setdefault(x, len(d)) for x in v))

def rot(w, delta=1):
    v = w[:-1]
    delta %= len(v)
    v = v[delta:] + v[:delta]
    return norm(v + (v[0],))

def metadata(w):
    edges = Counter((tuple(sorted(e)) for e in zip(w, w[1:])))
    adj = [[] for _ in range(max(w) + 1)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    depth = [None] * len(adj)
    depth[w[0]] = 0
    q = deque([w[0]])
    while q:
        a = q.popleft()
        for b in adj[a]:
            if depth[b] is None:
                depth[b] = depth[a] + 1
                q.append(b)
    member = max(depth) <= 2 and all((c == 2 for (a, b), c in edges.items() if min(depth[a], depth[b]) == 1))
    return (len(edges), member)

def walks(k):
    adj = [[]]
    depth = [0]
    path = [0]

    def rec(t, v):
        left = 2 * k - t
        if depth[v] > left:
            return
        if left == 0:
            if v == 0:
                yield tuple(path)
            return
        for u in tuple(adj[v]):
            path.append(u)
            yield from rec(t + 1, u)
            path.pop()
        if len(adj) <= k and depth[v] + 1 <= left - 1:
            u = len(adj)
            adj.append([v])
            adj[v].append(u)
            depth.append(depth[v] + 1)
            path.append(u)
            yield from rec(t + 1, u)
            path.pop()
            depth.pop()
            adj[v].pop()
            adj.pop()
    yield from rec(0, 0)
existing = json.load(open(OUT / 'recurrence_reference.json'))['rows']
checks = []
for k in range(1, 9):
    W = set(walks(k))
    require(len(W) == existing[k]['M2k'], (k, len(W)))
    A = {w for w in W if metadata(w)[1]}
    RA = {rot(w) for w in A}
    require(all((rot(rot(w), -1) == w for w in W)), 'verification failed: all((rot(rot(w), -1) == w for w in W))')
    require(RA <= W, 'verification failed: RA <= W')
    inter = A & RA
    union = A | RA
    require(len(A) == B[k + 1] - B[k], 'verification failed: len(A) == B[k + 1] - B[k]')
    require(len(inter) == F[2 * k], 'verification failed: len(inter) == F[2 * k]')
    require(len(union) == 2 * (B[k + 1] - B[k]) - F[2 * k], 'verification failed: len(union) == 2 * (B[k + 1] - B[k]) - F[2 * k]')
    by_l = {name: Counter((metadata(w)[0] for w in ws)) for name, ws in [('A', A), ('overlap', inter), ('union', union)]}
    for l in range(1, k + 1):
        L = sum((comb(k - 1, s) * S[k - s][l - s] for s in range(l)))
        O = comb(2 * k - l, l - 1)
        require(by_l['A'][l] == L, "verification failed: by_l['A'][l] == L")
        require(by_l['overlap'][l] == O, "verification failed: by_l['overlap'][l] == O")
        require(by_l['union'][l] == 2 * L - O, "verification failed: by_l['union'][l] == 2 * L - O")
    row = {'k': k, 'M2k': len(W), 'family_A': len(A), 'rotated_family': len(RA), 'overlap': len(inter), 'union_bound': len(union), 'coefficient_counts': by_l}
    checks.append(row)
    print('exhaustive', k, len(W), len(A), len(inter), len(union), flush=True)
bounds = []
for k in range(1, N + 1):
    row = existing[k]
    L = [0] + [sum((comb(k - 1, s) * S[k - s][l - s] for s in range(l))) for l in range(1, k + 1)]
    O = [0] + [comb(2 * k - l, l - 1) for l in range(1, k + 1)]
    U = [2 * x - y for x, y in zip(L, O)]
    require(all((0 <= a <= b for a, b in zip(U, row['edge_coefficients']))), "verification failed: all((0 <= a <= b for a, b in zip(U, row['edge_coefficients'])))")
    require(sum(U) == 2 * (B[k + 1] - B[k]) - F[2 * k], 'verification failed: sum(U) == 2 * (B[k + 1] - B[k]) - F[2 * k]')
    bounds.append({'k': k, 'Bell': B[k], 'next_Bell': B[k + 1], 'Fibonacci_2k': F[2 * k], 'lower_bound': sum(U), 'M2k': row['M2k'], 'coefficient_lower_bounds': U})
# Exact polynomial check of the weighted overlap recurrence, independent of alpha.
def poly_add(a, b, sign=1):
    c = [0] * max(len(a), len(b))
    for i, x in enumerate(a): c[i] += x
    for i, x in enumerate(b): c[i] += sign*x
    while len(c)>1 and c[-1]==0: c.pop()
    return c
P = [[0]] + [[0]+[comb(2*k-l,l-1) for l in range(1,k+1)] for k in range(1,N+1)]
require(P[1] == [0,1] and P[2] == [0,1,2], 'weighted initial polynomials')
for k in range(3,N+1):
    rhs = poly_add(poly_add(P[k-1],[0]+[2*x for x in P[k-1]]),[0,0]+P[k-2],-1)
    require(P[k] == rhs, ('weighted recurrence',k))
# Check the omitted four-edge-path witness for every tested k.
for k in range(4,N+1):
    w = (0,1,2,3,4,3,2,1,0)+(1,0)*(k-4)
    require(len(w)==2*k+1 and metadata(w)[0]==4, ('witness length/edges',k))
    require(not metadata(w)[1] and not metadata(rot(w,-1))[1], ('strict witness',k))
# Weighted Touchard form against the coefficient formula at rational alpha.
from fractions import Fraction
alphas = [Fraction(0),Fraction(1,3),Fraction(1),Fraction(2),Fraction(7,2)]
for k in range(1,N+1):
    for alpha in alphas:
        direct=sum(bounds[k-1]['coefficient_lower_bounds'][l]*alpha**l for l in range(k+1))
        touch=sum(comb(k-1,s)*alpha**s*sum(S[k-s][t]*alpha**t for t in range(k-s+1)) for s in range(k))
        overlap=sum(P[k][l]*alpha**l for l in range(k+1))
        require(direct==2*touch-overlap, ('weighted formula',k,str(alpha)))
        exact=sum(existing[k]['edge_coefficients'][l]*alpha**l for l in range(k+1))
        require(exact>=direct, ('weighted inequality',k,str(alpha)))
        require((exact==direct)==(alpha==0 or k<=3), ('weighted equality',k,str(alpha)))
result = {'status': 'passed', 'exhaustive_max_k': 8, 'recurrence_comparison_max_k': N, 'finite_checks_are_not_all_k_proof': True, 'explicit_guard_calls': CHECKS, 'weighted_polynomials_checked_through': N, 'weighted_rational_parameters': [str(x) for x in alphas], 'strict_witness_checked_through':N, 'exhaustive': checks, 'bounds': bounds}
(OUT / 'exact_checks.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print('PASS', flush=True)
