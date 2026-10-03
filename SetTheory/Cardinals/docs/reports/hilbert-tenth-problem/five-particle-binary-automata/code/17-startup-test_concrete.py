#!/usr/bin/env python3
# Verification conditions are explicit and remain active under python -O.
"""Supplementary literal-row replays. These are not the unbounded proof."""
from verify_pins import verify_inputs
verify_inputs()
import json
from pathlib import Path
from collections import defaultdict, Counter
from loader import from_counters, from_tape, five_particle_input, target_ledger
ROOT = Path(__file__).resolve().parent
stats = Counter()
C = json.loads((ROOT / 'certificates.json').read_text())

def read(name):
    M = json.loads((ROOT / name).read_text())
    g = defaultdict(list)
    for e in M['rows']:
        g[e['source']].append(e)
    return (M, g)
R, rg = read('reversible5.json')
P, pg = read('reversible2-primitives.json')
N, ng = read('normalized3.json')
V = json.loads((ROOT / 'dependency/virtual3.json').read_text())

def step(g, q, r):
    es = [e for e in g[q] if e['symbol'] not in 'ZP-' or (r[e['counter']] == 0 if e['symbol'] == 'Z' else r[e['counter']] > 0)]
    if not len(es) == 1:
        raise AssertionError((q, r, es))
    e = es[0]
    r = list(r)
    r[e['counter']] += {'+': 1, '-': -1}.get(e['symbol'], 0)
    return (e['target'], tuple(r))

def run(g, q, r, stops, budget=1000000):
    for n in range(1, budget + 1):
        q, r = step(g, q, r)
        if q in stops:
            return (q, r, n)
    raise RuntimeError(('Budget', q, r))
reps = {}
for c in C['prime']:
    reps.setdefault((c['kind'], c.get('prime'), tuple(sorted(c.get('targets', {})))), c)
for c in reps.values():
    p = c.get('prime')
    kind = c['kind']
    for n in range(33):
        if kind == '-':
            if n % p:
                continue
            value = n // p
            clock = 4 * n + (p + 3) * value + 3
            target = c['target']
        elif kind == '+':
            value = n * p
            clock = (p + 7) * n + 3
            target = c['target']
        elif kind == '0':
            value = n
            clock = 1
            target = c['target']
        else:
            b = 'P' if n % p == 0 else 'Z'
            if b not in c['targets']:
                continue
            value = n
            clock = 4 * n + 4 * (n // p) + 3
            target = c['targets'][b]
        actual = run(pg, c['source'], (n, 0), set(R['controls']))
        if not actual == (target, (value, 0), clock):
            raise AssertionError((c, n, actual, clock))
        stats['prime_macro_cases'] += 1
        stats['prime_literal_steps'] += clock
nr = {e['name']: e for e in N['rows']}
for c in C['history']:
    for b, name in enumerate(c['incoming']):
        e = nr[name]
        for h in range(5):
            r = [2, 3, 4, h, 0]
            i = e['counter']
            x = e['symbol']
            if x == 'Z':
                r[i] = 0
            out = r.copy()
            out[i] += {'+': 1, '-': -1}.get(x, 0)
            out[3] = 2 * h + b
            clock = 10 * h + 4 + 2 * b
            actual = run(rg, e['source'], r, set(N['controls']))
            if not actual == (c['target'], tuple(out), clock):
                raise AssertionError((c, b, h, actual, out))
            stats['history_macro_cases'] += 1
            stats['history_literal_steps'] += clock
for l, r, t, c in [(0, 0, 0, 1), (1, 0, 0, 1), (0, 1, 0, 1), (0, 0, 0, 13), (0, 0, 1, 1)]:
    expected = run(rg, 'START', (l, r, t, 0, 0), {V['entry']})
    q, regs, n = expected
    A = 1
    for p, v in zip((2, 3, 5, 7, 11), regs):
        A *= p ** v
    data = from_counters(l, r, t, c)
    actual = run(pg, 'START', (data['counter0'], 0), {V['entry']}, budget=1000000)
    if not actual[:2] == (q, (c * A, 0)):
        raise AssertionError('Verification obligation failed')
    stats['literal_end_to_end_entry_cases'] += 1
    stats['literal_end_to_end_entry_steps'] += actual[2]
pred = []
for l, r, t, c in [(0, 0, 0, 1), (1, 0, 0, 1), (0, 1, 0, 1), (0, 0, 0, 13), (0, 0, 1, 1)]:
    q = 'START'
    rs = (l, r, t, 0, 0)
    clock = 0
    steps5 = 0
    while q != V['tm_cuts']['A0']:
        es = [e for e in rg[q] if e['symbol'] not in 'ZP-' or (rs[e['counter']] == 0 if e['symbol'] == 'Z' else rs[e['counter']] > 0)]
        if not len(es) == 1:
            raise AssertionError('Verification obligation failed')
        e = es[0]
        n = c
        for pp, vv in zip((2, 3, 5, 7, 11), rs):
            n *= pp ** vv
        pp = (2, 3, 5, 7, 11)[e['counter']]
        s = e['symbol']
        clock += 1 if s == '0' else (pp + 7) * n + 3 if s == '+' else 4 * n + (pp + 3) * (n // pp) + 3 if s == '-' else 4 * n + 4 * (n // pp) + 3
        q, rs = step(rg, q, rs)
        steps5 += 1
    if not (rs[:3] == (l, r, 0) and rs[4] == 0):
        raise AssertionError('Verification obligation failed')
    pred.append(dict(input_LRT_cofactor=[l, r, t, c], final5=list(rs), five_counter_steps=steps5, predicted_two_counter_steps=clock))
(ROOT / 'prologue-predicted-clocks.json').write_text(json.dumps(dict(scope='Exact theorem-derived clocks; separately traversed T=0 cases are in initialization-receipt.json; T>0 cases here were not traversed at the two-counter level', cases=pred), indent=2) + '\n')
if not from_tape('101', '01') == from_counters(5, 2):
    raise AssertionError('Verification obligation failed')
G = target_ledger()
data = from_tape('', '')
coords = five_particle_input(data)
if not (len(set(coords)) == 5 and coords == [-G['Z'] - 1, 0, G['S'], G['S'] + 1, G['Z']]):
    raise AssertionError('Verification obligation failed')
(ROOT / 'target-ledger.json').write_text(json.dumps(G, indent=2) + '\n')
(ROOT / 'loader-empty-tape.json').write_text(json.dumps(dict(input=data, particles=coords), indent=2) + '\n')
out = dict(status='passed', checks=dict(stats), scope='Finite supplements to the affine/invariant proof; no universal run or eager CA allocation claimed')
(ROOT / 'concrete-receipt.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
