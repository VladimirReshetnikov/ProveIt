"""Finite inductive register invariant and physically used row census.

Domain for each logical register: subsets of {0,...,K-1, [K,infinity)}.
The product domain loses correlations but preserves all reachable states.
No SMT solver, arithmetic sampling, or consistency assumption is used.
"""
from pathlib import Path
import collections, json, sys, time
P = (Path(__file__).resolve().parent / 'reference_pa195')
sys.path.insert(0, str(P))
import build_verify as v
c = v.c
OUT = Path(__file__).resolve().parent
S = OUT / 'pa195_scanner8' if '--scanner8' in sys.argv else P
is8 = S != P
K = 4
OVER = 1 << K
TOP = (OVER << 1) - 1
t = c.read_grammar(S / 'grammar.json')
sites, cfg, contracts = c.source(t)
rows = v.table(S / ('pa195_scanner8.native.tm' if is8 else 'pa195.native.tm'))

def inc(mask):
    return ((mask << 1) & TOP) | (mask & OVER)

def dec(mask):
    return (mask >> 1) | (mask & OVER)

def successors(i, a):
    code = cfg[i]
    if code[0] == 'inc':
        _, reg, nxt = code
        b = list(a); b[reg] = inc(a[reg]); return [(nxt, tuple(b))]
    if code[0] == 'dec':
        _, reg, zero, positive = code
        out = []
        if a[reg] & 1:
            b = list(a); b[reg] = 1; out.append((zero, tuple(b)))
        if a[reg] & ~1:
            b = list(a); b[reg] = dec(a[reg] & ~1); out.append((positive, tuple(b)))
        return out
    if code[0] == 'jump':
        return [(code[1], a)]
    return []

abstract = [None] * len(cfg)
abstract[25] = (1 << 2,) + (1,) * 8
queue, queued = collections.deque([25]), {25}
steps = 0
while queue:
    i = queue.popleft(); queued.remove(i); steps += 1
    for j, a in successors(i, abstract[i]):
        old = abstract[j]
        joined = a if old is None else tuple(x | y for x, y in zip(old, a))
        if joined != old:
            abstract[j] = joined
            if j not in queued:
                queue.append(j); queued.add(j)
# Independently check the finite table's inductiveness, not worklist history.
v.need(all((seed & inv) == seed for seed, inv in
           zip((1 << 2,) + (1,) * 8, abstract[25])), 'seed outside invariant')
for i, a in enumerate(abstract):
    if a is None:
        continue
    for j, b in successors(i, a):
        v.need(abstract[j] is not None and all((x & y) == x for x, y in
                                             zip(b, abstract[j])), 'noninductive row')
kept, removed = [], []
for case in contracts:
    i, branch, initial, final = case
    a = abstract[i]
    allowed = a is not None
    if allowed and branch is not None:
        reg = cfg[i][1]
        allowed = bool(a[reg] & (1 if branch[1] else ~1))
    (kept if allowed else removed).append(case)
used = {(q, b) for q in c.BOXSTATES for b in (0, 1)}
def observe(s):
    q, onleft, left, right = s
    if onleft or not right:
        return
    x = right[0]
    if x[0] == 'b' or (x[0] == 'r' and (x[2] > 0 or x[3] > 0)):
        used.add((q, x[1]))
    elif x[0] == 'x':
        used.add((q, 0))
runtime = c.validate(rows, kept, observe=observe)
v.need(runtime['ok'], 'starting runtime failure')
q, head, ones = 74, 0, set()
for _ in range(59164 if is8 else 58154):
    bit = int(head in ones); used.add((q, bit)); w, d, q = rows[q, bit]
    (ones.add if w else ones.discard)(head); head += 1 if d else -1
unused = sorted(set(rows) - used)
result = {'domain_cutoff': K, 'over_bit': OVER, 'worklist_updates': steps,
          'reachable_sites': sum(x is not None for x in abstract),
          'all_sites': len(sites), 'kept_contracts': len(kept),
          'removed_contracts': [[x[0], x[1]] for x in removed],
          'runtime': runtime, 'unused_rows': unused, 'invariant': abstract}
name = 'scanner8_abstract_invariant.json' if is8 else 'abstract_invariant.json'
(OUT / name).write_text(json.dumps(result, indent=2))
print(json.dumps({k: val for k, val in result.items() if k != 'invariant'}, indent=2))
