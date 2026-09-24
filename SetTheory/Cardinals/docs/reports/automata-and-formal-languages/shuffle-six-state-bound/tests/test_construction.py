#!/usr/bin/env python3
"""Exhaustive small-grid and reproducible larger-grid access-word tests."""
from __future__ import annotations
import json
import random
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'python'))
from construct_word import Constructor, step, valid


def main() -> None:
    constructor = Constructor()
    trials = 0
    for m, n in [(1, 1), (1, 4), (2, 2), (2, 3), (2, 4), (3, 3)]:
        count = 0
        starts = [(i, j) for i in range(m) for j in range(n)] if (m, n) == (2, 2) else [(0, 0)]
        for start in starts:
            for mask in range(1 << (m*n)):
                S = {(i, j) for i in range(m) for j in range(n) if (mask >> (n*i+j)) & 1}
                if valid(S, start):
                    constructor.construct(m, n, S, start)
                    count += 1
        print(f'Complete valid-subset tests {m}x{n}, {len(starts)} anchors: {count} PASS')
        trials += count
    rng = random.Random(20260920)
    cases = []
    for m, n in [(6, 7), (6, 12), (6, 20), (6, 21), (6, 40), (12, 6)]:
        for _ in range(5):
            start = (rng.randrange(m), rng.randrange(n))
            S = {(i, j) for i in range(m) for j in range(n) if rng.random() < 0.4}
            S.add((start[0], rng.randrange(n)))
            S.add((rng.randrange(m), start[1]))
            cases.append((m, n, S, start))
    cores = []
    for (m, family) in constructor.certificates:
        if m == 6:
            columns = [c for c in range(64) if (family >> c) & 1]
            cores.append(columns)
    for columns in rng.sample(cores, 30):
        p = list(range(6)); rng.shuffle(p)
        q = list(range(len(columns))); rng.shuffle(q)
        S = {(p[i], q[j]) for j, c in enumerate(columns) for i in range(6) if (c >> i) & 1}
        cases.append((6, len(columns), S, (rng.randrange(6), rng.randrange(len(columns)))))
    # The largest-width core, all 3-element subsets of six rows.
    columns = [c for c in range(64) if c.bit_count() == 3]
    S = {(i, j) for j, c in enumerate(columns) for i in range(6) if (c >> i) & 1}
    cases.append((6, 20, S, (0, 0)))
    lengths = []
    for m, n, S, start in cases:
        word = constructor.construct(m, n, S, start)
        lengths.append({'m': m, 'n': n, 'cells': len(S), 'length': len(word),
                        'bound': len(S)+min(m, n)-2})
    trials += len(cases)
    print(f'Additional random/permuted-core/extreme cases: {len(cases)} PASS')
    print(f'Total access-word checks: {trials} PASS')
    # Independent singleton-distinguishing-word checks for the three letters.
    singleton_checks = 0
    for m in range(2, 7):
        for n in range(2, 9):
            alphabet = {
                'a': ([(i+1) % m for i in range(m)], [0]*n),
                'b': ([0]*m, [(j+1) % n for j in range(n)]),
                'c': ([1]+[0]*(m-1), [n-1]*n)}
            for i in range(m):
                for j in range(n):
                    if j >= 1:
                        word = 'a'*(m-1-i)+'b'*(n-1-j)
                    elif i >= 1:
                        word = 'b'+'a'*(m-1-i)+'b'*(n-2)
                    else:
                        word = 'cb'+'a'*(m-2)+'b'*(n-2)
                    accepted_from = set()
                    for r in range(m):
                        for c in range(n):
                            reached = {(r, c)}
                            for a in word:
                                reached = step(reached, alphabet[a])
                            if (m-1, n-1) in reached:
                                accepted_from.add((r, c))
                    if accepted_from != {(i, j)}:
                        raise ValueError(('distinguishing word', m, n, i, j))
                    singleton_checks += 1
    print(f'Explicit singleton-distinguishing words: {singleton_checks} PASS')
    (ROOT/'audit/construction_cases.json').write_text(json.dumps(lengths, indent=2)+'\n')
    print('OVERALL: PASS')


if __name__ == '__main__':
    main()
