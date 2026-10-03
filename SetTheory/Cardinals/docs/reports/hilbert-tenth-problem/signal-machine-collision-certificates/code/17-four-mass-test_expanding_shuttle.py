#!/usr/bin/env python3
"""Exact guarded conservative weighted CA and its non-semilinear hit times.

Alphabet: 0, u, R, L; weights: 0,1,2,2. Radius at most 6.
This is a typed weighted example, not an ordinary numerical-state encoding.
Only Python's standard library is used. No imported release files are changed.
"""
from itertools import product
import json
from pathlib import Path

WEIGHT = {'u': 1, 'R': 2, 'L': 2}
ALPHABET = (None, 'u', 'R', 'L')


def step(c):
    """Apply disjoint rewrites selected from the input configuration."""
    heads = [x for x, a in c.items() if a in ('R', 'L')]
    edits = {}
    for x in heads:
        if any(y != x and abs(y-x) <= 4 for y in heads):
            continue
        a = c[x]
        if a == 'R':
            if x+1 not in c:
                edits[x], edits[x+1] = None, 'R'
            elif c[x+1] == 'u' and x+2 not in c:
                edits[x], edits[x+1], edits[x+2] = 'L', None, 'u'
        else:
            if x-1 not in c:
                edits[x], edits[x-1] = None, 'L'
            elif c[x-1] == 'u':
                # The left marker stays put; only the head reverses.
                edits[x] = 'R'
    out = dict(c)
    for x, a in edits.items():
        if a is None:
            out.pop(x, None)
        else:
            out[x] = a
    return out


def mass(c):
    return sum(WEIGHT[a] for a in c.values())


def translated(c, a):
    return {x+a: s for x,s in c.items()}


def run():
    conservation_cases = 0
    for word in product(ALPHABET, repeat=8):
        c = {i:a for i,a in enumerate(word) if a is not None}
        assert mass(step(c)) == mass(c), c
        conservation_cases += 1
    trajectory_steps = 0
    hits_checked = 0
    for d in range(3, 20):
        c = {0:'u', 1:'R', d:'u'}
        expected = {k*k+(2*d-3)*k for k in range(101)}
        horizon = 100*100+(2*d-3)*100
        actual = set()
        for t in range(horizon+1):
            if c.get(0) == 'u' and c.get(1) == 'R':
                actual.add(t)
                k = len(actual)-1
                assert c == {0:'u', 1:'R', d+k:'u'}
                hits_checked += 1
            if t < horizon:
                c = step(c)
                trajectory_steps += 1
                assert mass(c) == 4
        assert actual == expected, (d, actual ^ expected)
    # A local output at 0 depends only on the radius-six input.
    locality_cases = 0
    import random
    rng = random.Random(43006)
    for _ in range(10000):
        c = {i:rng.choice(ALPHABET) for i in range(-12,13)}
        c = {i:a for i,a in c.items() if a is not None}
        local = {i:a for i,a in c.items() if abs(i)<=6}
        assert step(c).get(0) == step(local).get(0)
        assert step(translated(c,12345)) == translated(step(c),12345)
        locality_cases += 1
    result = {
        'status':'PASS', 'radius_upper_bound':6,
        'weights':WEIGHT, 'ordinary_numerical_state_CA':False,
        'dense_conservation_cases':conservation_cases,
        'direct_trajectory_steps':trajectory_steps,
        'predicted_hit_times_checked':hits_checked,
        'random_locality_and_translation_cases':locality_cases,
        'hit_formula':'t_k = k^2 + (2*d - 3)*k for initial u@0,R@1,u@d, d>=3',
        'proof_limit':'Finite tests supplement the disjoint rewrite proof; they are not the theorem proof.'
    }
    out = Path(__file__).with_name('shuttle-test-results.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    run()
