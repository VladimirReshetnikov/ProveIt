#!/usr/bin/env python3
"""Compile calibrated implication/falsum A10 and dual-B source experiments.

Walsh--Fitelson A10: CCCpqCrsCCsCrCrfCrp.  Its single-occurrence
parameter q reuses the exact existing stream reader.  Every replacement
chunk is closed in the structured source language.
"""
from pathlib import Path
from functools import cache
import itertools
import json
import os
import sys

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'k220_replay/baseline/K221_Construction_2026-10-20'
ENC = ROOT / 'baseline220/K220_Construction_2026-10-20/research/encoding/scripts'
os.environ['K221_BASE'] = str(BASE)
os.environ['ENCODING_OUTPUT'] = str(ROOT / 'theory_notes/a10_search_support')
sys.path.insert(0, str(ENC / 'rows'))
sys.path.insert(0, str(ENC))
import search as z
sys.path.insert(0, str(ROOT / 'source_work'))
import hardware_objective as hw

s, b = z.s, z.b
old = s.tree(json.loads((ROOT / 'baseline220/K220_Construction_2026-10-20/machine/sites220.json').read_text()))
table = b.read_table((ROOT / 'baseline220/K220_Construction_2026-10-20/machine/k220.native.tm').read_bytes())
OUT = ROOT / 'theory_notes/a10_variants'
OUT.mkdir(exist_ok=True)


def chunks(tree, lo, hi):
    found = []
    def visit(n, st=0):
        en = st + len(z.flat(n))
        if en <= lo or st >= hi:
            return
        if lo <= st and en <= hi:
            assert s.boundary(n) == (0, 0, False), (st, en)
            found.append((st, en, n))
            return
        assert not s.leaf(n)
        visit(n[0], st)
        visit(n[1], st + len(z.flat(n[0])))
    visit(tree)
    assert found[0][0] == lo and found[-1][1] == hi
    assert all(x[1] == y[0] for x, y in zip(found, found[1:]))
    return found


def splice(tree, lo, hi, new, insert_last=False):
    assert s.boundary(new) == (0, 0, False)
    cc = chunks(tree, lo, hi)
    target = cc[-1][0] if insert_last else lo
    def visit(n, st=0):
        en = st + len(z.flat(n))
        if en <= lo or st >= hi:
            return n
        if lo <= st and en <= hi:
            return new if st == target else None
        left = visit(n[0], st)
        right = visit(n[1], st + len(z.flat(n[0])))
        return right if left is None else left if right is None else (left, right)
    answer = visit(tree)
    assert z.flat(answer) == z.flat(tree)[:lo] + z.flat(new) + z.flat(tree)[hi:]
    return answer


reader = z.seq([n for _, _, n in chunks(old, 161, 194)])
assert s.boundary(reader) == (0, 0, False)
assert all(not (op in ('CI', 'CD') and arg in (3, 4, 5))
           for op, arg in z.flat(reader))


def parse_polish(word):
    def go(i):
        if word[i] != 'C':
            return word[i], i + 1
        l, i = go(i + 1)
        r, i = go(i)
        return ('I', l, r), i
    formula, end = go(0)
    assert end == len(word)
    return formula


A10 = parse_polish('CCCpqCrsCCsCrCrfCrp')


def a10_atoms(permutation):
    pushes = dict(zip(('p', 'r', 's'), permutation))
    pushes.update(q=reader, f=z.MACRO[177])
    def go(formula):
        if isinstance(formula, str):
            return [pushes[formula]]
        _, l, r = formula
        if r == 'f':
            return go(l) + [z.MACRO[218]]
        return go(l) + go(r) + [z.MACRO[119]]
    return go(A10)


def dual_b_atoms(binder, matrix):
    return [matrix, binder, binder, matrix, z.MACRO[183],
            z.MACRO[180], z.MACRO[119]]


def main():
    results = []
    pushes = (z.MACRO[166], z.MACRO[121], z.MACRO[168])
    best = 999
    objective = hw.make(table, old)[0]
    for ai, perm in enumerate(itertools.permutations(pushes)):
        a10 = z.seq(a10_atoms(perm))
        for bi, pair in enumerate([None] + list(itertools.permutations(pushes, 2))):
            dual = None if pair is None else z.seq(dual_b_atoms(*pair))
            for last8, last6 in itertools.product((False, True), repeat=2):
                new = old
                if dual is not None:
                    new = splice(new, 895, 1178, dual, last6)
                new = splice(new, 135, 486, a10, last8)
                metrics = s.metrics(new)
                result = {'A10_parameters': ai, 'rho6_variant': bi,
                          'insert_last': [last8, last6], 'metrics': metrics}
                rows = s.sites(new)
                assert s.graph_arithmetic(rows)[0] == s.graph_intervals(rows)
                result['hardware_lower_bound'] = objective(new)
                cost = result['hardware_lower_bound']['cost_lower_bound']
                if cost < best:
                    best = cost
                    print('BEST', json.dumps(result), flush=True)
                    d = OUT / f'a{ai}_b{bi}_i{int(last8)}{int(last6)}'
                    d.mkdir(exist_ok=True)
                    (d / 'sites.json').write_bytes(s.compact(rows))
                    (d / 'receipt.json').write_text(json.dumps(result, indent=2) + '\n')
                results.append(result)
    (OUT / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print('COMPLETE', len(results), 'best hardware lower bound', best)


if __name__ == '__main__':
    main()
