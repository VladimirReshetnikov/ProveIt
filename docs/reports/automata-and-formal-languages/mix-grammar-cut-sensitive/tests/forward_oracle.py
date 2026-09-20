#!/usr/bin/env python3
"""Independent, forward-only saturation of the *original* fixed-arity rules.

This deliberately does not use the backward parser to generate accepted tuples.
All exact r-tuples, including empty components, are retained.
"""
from __future__ import annotations
from itertools import combinations, combinations_with_replacement, permutations
from pathlib import Path
import json
import sys
import time
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from mix_parser import Parser


def regroup(parts: tuple[str, ...], r: int):
    for cuts in combinations_with_replacement(range(len(parts) + 1), r - 1):
        bounds = (0,) + cuts + (len(parts),)
        yield tuple(''.join(parts[bounds[i]:bounds[i + 1]]) for i in range(r))


def forward(r: int, max_length: int):
    levels = {0: {('',) * r}}
    slots = tuple(combinations(range(2 * r), 3))
    letters = tuple(permutations('abc'))
    for n in range(3, max_length + 1, 3):
        seeds = set()
        for child in levels[n - 3]:
            for chosen in slots:
                for abc in letters:
                    ends = [''] * (2 * r)
                    for j, c in zip(chosen, abc):
                        ends[j] = c
                    seeds.add(tuple(ends[2*i] + child[i] + ends[2*i+1]
                                    for i in range(r)))
        for n1 in range(3, n, 3):
            for u in levels[n1]:
                for v in levels[n - n1]:
                    for gap in range(r + 1):
                        seeds.update(regroup(u[:gap] + v + u[gap:], r))
        # A binary rule with an empty child is precisely regrouping. Regrouping
        # is idempotent, so this one closure pass accounts for arbitrarily many.
        closed = set()
        for t in seeds:
            closed.update(regroup(t, r))
        levels[n] = closed
    return levels


def balanced_words(k: int):
    n = 3*k
    for aa in combinations(range(n), k):
        aset = set(aa)
        rem = [i for i in range(n) if i not in aset]
        for bb in combinations(rem, k):
            bset = set(bb)
            yield ''.join('a' if i in aset else 'b' if i in bset else 'c'
                          for i in range(n))


def run():
    result = []
    for r in (1, 2, 3):
        start = time.perf_counter()
        levels = forward(r, 6)
        parser = Parser(r)
        rows = []
        for n, accepted in levels.items():
            checked = 0
            for w in balanced_words(n // 3):
                for cuts in combinations_with_replacement(range(n + 1), r - 1):
                    b = (0,) + cuts + (n,)
                    t = tuple(w[b[i]:b[i+1]] for i in range(r))
                    answer = parser.accepts(t)
                    if answer != (t in accepted):
                        raise AssertionError((r, t, answer, t in accepted))
                    checked += 1
            rows.append({'length': n, 'tested_exact_tuples': checked,
                         'forward_accepted_exact_tuples': len(accepted)})
        result.append({'arity': r, 'rows': rows,
                       'seconds': time.perf_counter() - start})
    print(json.dumps({'all_checks_passed': True, 'results': result}, indent=2))

if __name__ == '__main__':
    run()
