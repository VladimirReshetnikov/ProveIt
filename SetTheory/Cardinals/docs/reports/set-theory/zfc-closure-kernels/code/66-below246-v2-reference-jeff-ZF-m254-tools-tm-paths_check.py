"""Check paths.json against CONTROL_GRAPH.json graph under Wade path semantics (RM.v)."""
import json, sys
from collections import Counter
D = sys.argv[1]
paths = json.load(open(D + '/paths.json'))
G = json.load(open(D + '/CONTROL_GRAPH.json'))
graph = G['graph']
assert len(paths) == len(graph)
assert all(p.startswith('110') for p, _ in paths)
body = [p[3:] for p, _ in paths]
# prefix-free & complete
S = set(body)
assert len(S) == len(body)
for b in body:
    for i in range(len(b)):
        assert b[:i] not in S, b
# completeness: every proper prefix node has both children as prefixes of some word
pref = set(b[:i] for b in body for i in range(len(b)))
for p in pref:
    for c in '01':
        assert (p + c) in pref or (p + c) in S, ('incomplete', p + c)
print('tree ok: leaves', len(body), 'internal', len(pref), 'max depth', max(map(len, body)))
idx = {b: i for i, b in enumerate(body)}
def walk(P):
    """return leaf index reached reading P with implicit trailing zeros, and depth"""
    i = 0
    while True:
        cur = P[:i] if i <= len(P) else P + '0' * (i - len(P))
        if cur in idx: return idx[cur], i
        i += 1
        assert i < 100
def inc(P):
    if '0' not in P: return ''
    j = P.rindex('0'); return P[:j] + '1'
def strip(b, k, P):
    while k > 0:
        if not P: return ''
        if P[-1] == b: k -= 1
        P = P[:-1]
    return P
def brk(k, P): return inc(strip('0', k, P))
def cont(k, P): return strip('1', k, P)
bad = Counter(); kinds = Counter(); ovf = []
for i, ((p, op), g) in enumerate(zip(paths, graph)):
    P = body[i]
    assert walk(P) == (i, len(P))
    if op.endswith('.inc'):
        assert g[0] == op and len(g) == 2
        succ = [(inc(P), g[1])]
        if '0' not in P: ovf.append((i, op))
    elif op.endswith('.decnz'):
        assert g[0] == op and len(g) == 3
        succ = [(inc(P), g[1]), (brk(1, P), g[2])]
        if '0' not in P: ovf.append((i, op))
    elif op.startswith('_continue'):
        k = int(op.split('.')[1]); assert g[0] == 'goto'
        succ = [(cont(k, P), g[1])]
    elif op.startswith('_break'):
        k = int(op.split('.')[1]); assert g[0] == 'goto'
        succ = [(brk(k, P), g[1])]
        if '0' not in strip('0', k, P): ovf.append((i, op))
    elif op == 'halt':
        assert g == ['halt'] or g[0] == 'halt', g; succ = []
    else:
        raise SystemExit('op ' + op)
    kinds[op.split('.')[0] if op.startswith('_') else op.split('.')[-1]] += 1
    for Q, t in succ:
        if walk(Q)[0] != t: bad[op] += 1
print('kinds', kinds); print('mismatches', bad); print('overflow-capable sites', ovf)
print('decnz paths ending in 1:', sum(1 for (p, op) in paths if op.endswith('decnz') and p.endswith('1')))
n = 0
for i, ((p, op), g) in enumerate(zip(paths, graph)):
    P = body[i]
    if op.endswith('.inc'):
        Q = inc(P); t = walk(Q)[0]
        if t != g[1] and n < 8:
            n += 1
            print(i, op, P, '-> inc', Q, 'walks to', t, paths[t], 'graph says', g[1], paths[g[1]], G['source_graph'][i])
def resolve(t, seen=()):
    while graph[t][0] == 'goto':
        t = graph[t][1]
    return t
bad2 = Counter(); direct = Counter()
for i, ((p, op), g) in enumerate(zip(paths, graph)):
    P = body[i]
    if op.endswith('.inc'): succ = [(inc(P), g[1])]
    elif op.endswith('.decnz'): succ = [(inc(P), g[1]), (brk(1, P), g[2])]
    elif op.startswith('_continue'): succ = [(cont(int(op.split('.')[1]), P), g[1])]
    elif op.startswith('_break'): succ = [(brk(int(op.split('.')[1]), P), g[1])]
    else: succ = []
    for Q, t in succ:
        w = walk(Q)[0]
        if w == t: direct['eq'] += 1
        elif resolve(w) == resolve(t): direct['eq-mod-goto'] += 1
        else: bad2[op] += 1
print('second check', direct, bad2)
