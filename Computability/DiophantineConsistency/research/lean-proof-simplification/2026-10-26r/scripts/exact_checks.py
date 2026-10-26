#!/usr/bin/env python3
"""Supplementary exact-integer experiments; these are not formal proofs."""
import json
from math import comb

def pell_pair(a, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = a*x + (a*a - 1)*y, x + a*y
    return x, y

counts = {}
count = 0
for H in range(41):
    for b in range(11):
        for r in range(9):
            if 2*r*b <= H:
                assert H*(H+b)**r <= H**r*(H+2*r*b)
                count += 1
counts['natural_perturbation_instances'] = count

count = 0
for a in range(1, 13):
    for b in range(a, 17):
        for n in range(13):
            xa, ya = pell_pair(a, n)
            xb, yb = pell_pair(b, n)
            assert xa <= xb and ya <= yb
            count += 1
counts['pell_base_comparisons'] = count

count = 0
even_count = 0
for r in range(1, 17):
    for X in [2**(2*r)+1, 2**(2*r)+2, 2**(2*r+1), 2**(2*r+1)+2]:
        T, D, C = (X+1)**(2*r), X**r, comb(2*r, r)
        L = sum(comb(2*r, j)*X**j for j in range(r))
        W = sum(comb(2*r, r+1+j)*X**j for j in range(r))
        assert T == D*(C+X*W)+L and 0 < L < D
        assert divmod(T, D) == (C+X*W, L)
        count += 1
        if X % 2 == 0:
            assert (C+X*W) % 2 == 0
            even_count += 1
counts['binomial_splits'] = count
counts['even_binomial_quotients'] = even_count

count = budget_count = 0
budget_counts_by_q = {q: 0 for q in [1, 2, 3]}
for U in [1, 2, 3, 16, 73, 145, 577]:
    for Y in range(1, 13):
        for r in range(1, 9):
            H = Y*(U+1)
            if H < max(16, 18*r):
                continue
            P = 2*U*Y**2+1
            D, T = U**r, (U+1)**(2*r)
            c, K = pell_pair(H+2, 2*r+1)[1], pell_pair(P, r+1)[1]
            Z, Q = (2*(H+2))**2*U, (2*P-1)*(U+1)**2
            assert Z*H <= Q*(H+9)
            assert c*D <= Z**r and Q**r <= K*T
            assert c*D*H <= K*T*(H+18*r)
            count += 1
            for q in [1, 2, 3]:
                if q*T*18*r < D*H:
                    assert q*c*D < K*(q*T+D)
                    budget_count += 1
                    budget_counts_by_q[q] += 1

# The small-Y grid above exercises majorants but need not satisfy any error
# budget.  Choose a second, deterministic set just beyond the q=3 threshold.
# These are actual positive Pell-sequence parameters, not claimed solutions
# of the full native source system.  Exact integer arithmetic checks both
# the growth/majorant premises and every q=1,2,3 conclusion.
targeted_count = 0
targeted_example = None
for U in [1, 2, 3, 16, 73, 145, 577]:
    for r in range(1, 9):
        D, T = U**r, (U+1)**(2*r)
        Y = (3*T*18*r) // (D*(U+1)) + 1
        H = Y*(U+1)
        assert H >= max(16, 18*r)
        P = 2*U*Y**2+1
        c, K = pell_pair(H+2, 2*r+1)[1], pell_pair(P, r+1)[1]
        Z, Q = (2*(H+2))**2*U, (2*P-1)*(U+1)**2
        assert Z*H <= Q*(H+9)
        assert c*D <= Z**r and Q**r <= K*T
        assert c*D*H <= K*T*(H+18*r)
        count += 1
        targeted_count += 1
        for q in [1, 2, 3]:
            assert q*T*18*r < D*H
            assert q*c*D < K*(q*T+D)
            budget_count += 1
            budget_counts_by_q[q] += 1
        if U == 73 and r == 1:
            targeted_example = dict(U=U, Y=Y, r=r, H=H, P=P, D=D, T=T,
                                    c=c, K=K, q=3,
                                    budget_slack=D*H-3*T*18*r,
                                    conclusion_slack=K*(3*T+D)-3*c*D)
assert targeted_count > 0 and all(n > 0 for n in budget_counts_by_q.values())
assert targeted_example is not None
counts['pell_majorants'] = count
counts['error_budget_instances'] = budget_count
counts['budget_targeted_pell_parameters'] = targeted_count
for q, n in budget_counts_by_q.items():
    counts[f'error_budget_q{q}_instances'] = n

count = 0
for D in range(1, 9):
    for k in range(1, 9):
        for t in range(6):
            for s in range(D):
                A = 2*t*D+s
                for c in range(k*(t+2)+2):
                    if k*A < 2*c*D < k*(A+D) and c % k:
                        Y = c // k
                        assert k*Y < c < k*(Y+1)
                        assert Y == t
                        count += 1
counts['strict_rounding_windows'] = count

example = dict(r=1, X=8, T=81, D=8, C=2, W=1, L=1, t=5, k=16, c=85, Y=5)
assert 16*81 < 2*85*8 < 16*(81+8)
assert 16*5 < 85 < 16*6
assert 2*5 == 2+8

# Removing the remainder bound permits the wrong interval index.
D, k, t, s, c, Y = 1, 4, 0, 2, 5, 1
A = 2*t*D+s
assert k*A < 2*c*D < k*(A+D) and k*Y < c < k*(Y+1) and Y != t
print(json.dumps({'all_passed': True, 'scope': 'finite exact-integer supplementary experiments',
                  'counts': counts, 'rounding_example': example,
                  'targeted_pell_budget_example': targeted_example,
                  'remainder_bound_negative_control': dict(D=D,k=k,t=t,s=s,c=c,Y=Y)}, indent=2))
