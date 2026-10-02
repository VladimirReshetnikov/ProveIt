#!/usr/bin/env python3
"""Exact finite checks. These do not prove asymptotic statements."""
from pathlib import Path
from collections import defaultdict
from fractions import Fraction
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent

def children(s, u, k):
    for i in range(s + u):
        if i < s:
            yield (s - 1, u + int(i >= k), i)
        else:
            yield (s + 1, u - int(i < k), i + 1)

checked = 0
for s in range(50):
    for u in range(1, (50 - s) // 2 + 1):
        m = s + u
        for k in range(m):
            cc = list(children(s, u, k))
            assert len(cc) == m
            assert sum(a + b for a, b, _ in cc) == m * m + u - k
            assert all(a >= 0 and b >= 1 and 0 <= c < a+b for a,b,c in cc)
            assert all(abs(a+b-m) <= 1 for a,b,_ in cc)
            assert u-k >= 2-m and abs(u-k) <= m
            checked += 1

states = {(0, 1, 0): 1}
counts = []
identities = 0
for n in range(21):
    a = sum(states.values())
    counts.append(a)
    mean = Fraction(sum(v*(s+u) for (s,u,k),v in states.items()), a)
    mean2 = Fraction(sum(v*(s+u)**2 for (s,u,k),v in states.items()), a)
    drift = Fraction(sum(v*(u-k) for (s,u,k),v in states.items()), a)
    nxt = defaultdict(int)
    for x,v in states.items():
        for y in children(*x):
            nxt[y] += v
    assert Fraction(sum(nxt.values()), a) == mean
    next_mean = Fraction(sum(v*(s+u) for (s,u,k),v in nxt.items()), sum(nxt.values()))
    assert next_mean == mean + (mean2-mean*mean+drift)/mean
    assert next_mean >= mean - 1 + 2/mean
    identities += 1
    states = nxt

frozen = json.loads((ROOT/'results/a_seq.json').read_text())
assert counts == frozen[:len(counts)]
assert frozen == json.loads((ROOT/'results/a_seq_m.json').read_text())
for n in range(1, len(frozen)-1):
    assert (n+1)*frozen[n]**2 >= n*frozen[n-1]*frozen[n+1]

print(json.dumps({'passed': True, 'state_transition_checks': checked,
                  'exact_forward_moment_identities': identities,
                  'root_counts_cross_checked_through': len(counts)-1,
                  'frozen_root_logconcavity_checked_through': len(frozen)-2}))
