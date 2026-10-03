#!/usr/bin/env python3
# Verification conditions are explicit and remain active under python -O.
"""Saved-row affine verification; does not import generation code.
All variables denote independent arbitrary naturals. Proof.md supplies induction.
"""
import json
from pathlib import Path
from collections import defaultdict, Counter
ROOT = Path(__file__).resolve().parent
C = json.loads((ROOT / 'certificates.json').read_text())
stats = Counter()

def load(name):
    m = json.loads((ROOT / name).read_text())
    d = defaultdict(list)
    for e in m['rows']:
        d[e['source']].append(e)
    return (m, d)
R, rg = load('reversible5.json')
P, pg = load('reversible2-primitives.json')
N, ng = load('normalized3.json')
nr = {e['name']: e for e in N['rows']}

def aff(c=0, *co):
    return (c,) + tuple(co) + (0,) * (5 - len(co))

def plus(a, c):
    return (a[0] + c,) + a[1:]
z = aff()
x = aff(0, 1)
y = aff(0, 0, 1)
v = aff(0, 0, 0, 1)

def zero(a):
    return a == z

def positive(a):
    return a[0] >= 1 and min(a[1:]) >= 0

def truth(e, regs):
    a = regs[e['counter']]
    s = e['symbol']
    if s == 'Z':
        if zero(a):
            return True
        if positive(a):
            return False
    elif s in 'P-':
        if zero(a):
            return False
        if positive(a):
            return True
    else:
        return True
    raise RuntimeError(('Unresolved affine guard', e, a))

def path(graph, start, regs, end, expected, length, cover):
    q = start
    regs = list(regs)
    for _ in range(length):
        enabled = [e for e in graph[q] if truth(e, regs)]
        if not len(enabled) == 1:
            raise AssertionError((q, regs, enabled))
        e = enabled[0]
        cover.add(e['name'])
        i = e['counter']
        s = e['symbol']
        if s in '+-':
            regs[i] = plus(regs[i], 1 if s == '+' else -1)
        if not all((a[0] >= 0 and min(a[1:]) >= 0 for a in regs)):
            raise AssertionError('Verification obligation failed')
        q = e['target']
    if not (q, tuple(regs)) == (end, tuple(expected)):
        raise AssertionError((start, q, regs, end, expected))
    stats['affine_paths'] += 1
rcov = set()
pcov = set()
changed = {n for h in C['history'] for n in h['incoming']}

def check_edge(e, cover):
    regs = [x, y, v, aff(0, 0, 0, 0, 1), aff(0, 0, 0, 0, 0, 1)]
    i = e['counter']
    s = e['symbol']
    if s == 'Z':
        regs[i] = z
    elif s in 'P-':
        regs[i] = plus(regs[i], 1)
    expected = list(regs)
    if s in '+-':
        expected[i] = plus(expected[i], 1 if s == '+' else -1)
    path(rg, e['source'], regs, e['target'], expected, 1, cover)
for e in R['rows']:
    if e['name'] in nr and e['name'] not in changed:
        check_edge(e, rcov)
for h in C['history']:
    d = h['doubling']
    pref = h['prefix']
    byname = {e['name']: e for e in R['rows'] if e['name'].startswith(pref)}
    for b, a in enumerate(h['parts']):
        check_edge(byname[pref + f'b{b}r0'], rcov)
        path(rg, a[0], (x, y, v, aff(0, 0, 0, 0, 1), z), a[1], (x, y, v, aff(0, 0, 0, 0, 1), z), 1, rcov)
        path(rg, a[1], (x, y, v, plus(aff(0, 0, 0, 0, 1), 1), aff(0, 0, 0, 0, 0, 1)), a[1], (x, y, v, aff(0, 0, 0, 0, 1), plus(aff(0, 0, 0, 0, 0, 1), 1)), 4, rcov)
        path(rg, a[1], (x, y, v, z, aff(0, 0, 0, 0, 0, 1)), d[0] if b == 0 else d[4], (x, y, v, z, aff(0, 0, 0, 0, 0, 1)), 1, rcov)
    path(rg, d[0], (x, y, v, aff(0, 0, 0, 0, 1), plus(aff(0, 0, 0, 0, 0, 1), 1)), d[0], (x, y, v, plus(aff(0, 0, 0, 0, 1), 2), aff(0, 0, 0, 0, 0, 1)), 6, rcov)
    path(rg, d[4], (x, y, v, z, aff(0, 0, 0, 0, 0, 1)), d[0], (x, y, v, aff(1), aff(0, 0, 0, 0, 0, 1)), 2, rcov)
    path(rg, d[0], (x, y, v, aff(0, 0, 0, 0, 1), z), h['target'], (x, y, v, aff(0, 0, 0, 0, 1), z), 1, rcov)
for c in C['prime']:
    q = c['source']
    a = c['prefix']
    kind = c['kind']
    if kind == '0':
        path(pg, q, (x, y), c['target'], (x, y), 1, pcov)
        continue
    p = c['prime']
    if kind in '+-':
        path(pg, q, (x, z), a + 'S1', (x, z), 1, pcov)
        path(pg, a + 'S1', (plus(x, 1), y), a + 'S1', (x, plus(y, 1)), 4, pcov)
        path(pg, a + 'S1', (z, y), a + 'S5', (z, y), 1, pcov)
        if kind == '+':
            path(pg, a + 'S5', (x, plus(y, 1)), a + 'S5', (plus(x, p), y), p + 3, pcov)
        else:
            path(pg, a + 'S5', (x, plus(y, p)), a + 'S5', (plus(x, 1), y), p + 3, pcov)
        path(pg, a + 'S5', (x, z), c['target'], (x, z), 1, pcov)
    else:
        path(pg, q, (x, z), a + 'R0T1', (x, z), 1, pcov)
        path(pg, a + 'R0T1', (plus(x, p), y), a + 'R0T1', (x, plus(y, 1)), 2 * p + 2, pcov)
        for r in range(p):
            kind = 'P' if r == 0 else 'Z'
            if kind in c['targets']:
                target = c['targets'][kind]
                rp = C['restoration'][target]['prefix']
                path(pg, a + 'R0T1', (aff(r), y), rp + f'R{r}T1', (z, y), 2 * r + 1, pcov)
for q, c in C['restoration'].items():
    a = c['prefix']
    p = c['prime']
    for r in range(1, p + 1):
        path(pg, a + f'R{r}T1', (x, y), a + 'R0T1', (plus(x, r), y), 2 * r, pcov)
    path(pg, a + 'R0T1', (x, plus(y, 1)), a + 'R0T1', (plus(x, p), y), 2 * p + 2, pcov)
    path(pg, a + 'R0T1', (x, z), q, (x, z), 1, pcov)
if not rcov == {e['name'] for e in R['rows']}:
    raise AssertionError(len({e['name'] for e in R['rows']} - rcov))
if not pcov == {e['name'] for e in P['rows']}:
    raise AssertionError(len({e['name'] for e in P['rows']} - pcov))
stats['reversible5_rows_covered'] = len(rcov)
stats['reversible2_rows_covered'] = len(pcov)
out = dict(status='passed', checks=dict(stats), scope='Affine paths on arbitrary naturals, every literal row; composed with invariants and decreasing ranks in PROOF.md')
(ROOT / 'affine-receipt.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
