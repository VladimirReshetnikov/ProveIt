"""Flatten the Wade-compiled program DAG (path semantics) into a flat goto-free op graph and compare it
with the third party's flat source graph (inputs/CONTROL_GRAPH.json, parsed as data only) by
bisimulation from the entries.

Flat op graph: node -> ('inc', reg, next) | ('decnz', reg, next_nonzero, next_zero) | ('halt',) | ('end',)
('end' = one run of main() finished, i.e. back at the program entry.)

Usage: python -I flatten.py [graph|source_graph]
"""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

def flatten_dag(nodes, root='main().0'):
    from rmsim import _exit
    def walk(P):
        cur = ('node', root); d = 0
        while cur[0] == 'node':
            b = P[d] if d < len(P) else 0
            cur = nodes[cur[1]][b]; d += 1
        return cur, (P + [0] * d)[:d]
    def norm(P):
        P = list(P)
        while P and P[-1] == 0:
            P.pop()
        return tuple(P)
    flat = {}; todo = [()]; seen = {()}
    def target(Q, ex):
        res = _exit(list(Q), ex)
        if res[0] == 'esc':
            assert res[1] == ('normal',), res
            return 'END'
        t = norm(res[1])
        if t == ():
            return 'END'
        if t not in seen:
            seen.add(t); todo.append(t)
        return t
    while todo:
        P = todo.pop()
        leaf, Q = walk(list(P))
        k = leaf[0]
        if k == 'halt':
            flat[P] = ('halt',)
        elif k == 'op' and leaf[2] == 'inc':
            flat[P] = ('inc', leaf[1], target(Q, ('normal',)))
        elif k == 'op':
            flat[P] = ('decnz', leaf[1], target(Q, ('normal',)), target(Q, ('break', 1)))
        elif k in ('break', 'continue'):
            flat[P] = ('goto', target(Q, leaf))
        else:
            raise ValueError(leaf)
    flat['END'] = ('end',)
    return flat, ()

def load_theirs(which='graph'):
    d = json.load(open(os.path.join(HERE, '..', 'inputs', 'CONTROL_GRAPH.json')))
    g = d[which]; entry = d['source_entry']
    flat = {}
    for i, e in enumerate(g):
        op = e[0]
        if op == 'goto':
            flat[i] = ('goto', 'END' if e[1] == entry else e[1])
        elif op == 'halt':
            flat[i] = ('halt',)
        else:
            _, reg, kind = op.split('.')
            ts = ['END' if (t == entry) else t for t in e[1:]]
            flat[i] = (kind, reg, *ts)
    flat['END'] = ('end',)
    return flat, entry

def skip_goto(flat, n):
    seen = set()
    while flat[n][0] == 'goto':
        assert n not in seen, 'goto cycle'
        seen.add(n); n = flat[n][1]
    return n

def bisim(f1, e1, f2, e2):
    """simultaneous exploration; returns (ok, pairs, mismatch)."""
    rel = {}; todo = [(e1, e2)]
    while todo:
        a, b = todo.pop()
        a = skip_goto(f1, a); b = skip_goto(f2, b)
        if a in rel:
            if rel[a] != b:
                # the same node of f1 related to two nodes of f2 is fine for bisimulation; record set
                rel.setdefault(('multi', a), set()).add(b)
            else:
                continue
        rel[a] = b
        x, y = f1[a], f2[b]
        if x[0] != y[0] or (x[0] in ('inc', 'decnz') and x[1] != y[1]):
            return False, len(rel), (a, x, b, y)
        if x[0] == 'inc':
            todo.append((x[2], y[2]))
        elif x[0] == 'decnz':
            todo.append((x[2], y[2])); todo.append((x[3], y[3]))
    return True, len(rel), None

if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'source_graph'
    from build_dag import load_dag
    nodes, regidx = load_dag()
    mine, e1 = flatten_dag(nodes)
    from collections import Counter
    print('mine: flat sites', len(mine), Counter(v[0] for v in mine.values()))
    theirs, e2 = load_theirs(which)
    print('theirs (%s): sites' % which, len(theirs), Counter(v[0] for v in theirs.values()))
    ok, n, mm = bisim(mine, e1, theirs, e2)
    print('bisimilar from entries:', ok, 'related pairs', n, mm or '')

def bisim_commuting(f1, e1, f2, e2):
    """bisimulation up to reordering of increments inside straight-line inc runs: explore triples
    (a, b, delta) where delta = increments done by f1 minus those done by f2 since the last test;
    tests (decnz), halt and end must be reached with delta = 0 on both sides."""
    from collections import Counter
    seen = set(); todo = [(e1, e2, ())]
    maxdelta = 0
    while todo:
        a, b, delta = todo.pop()
        a = skip_goto(f1, a); b = skip_goto(f2, b)
        key = (a, b, delta)
        if key in seen:
            continue
        seen.add(key)
        x, y = f1[a], f2[b]
        D = Counter(dict(delta))
        if x[0] == 'inc' or y[0] == 'inc':
            na, nb = a, b
            if x[0] == 'inc':
                D[x[1]] += 1; na = x[2]
            if y[0] == 'inc':
                D[y[1]] -= 1; nb = y[2]
            nd = tuple(sorted((r, c) for r, c in D.items() if c != 0))
            maxdelta = max(maxdelta, sum(abs(c) for _, c in nd))
            if maxdelta > 8:
                return False, len(seen), ('delta too large', a, x, b, y, nd)
            todo.append((na, nb, nd))
            continue
        if delta:
            return False, len(seen), ('pending increments at a test', a, x, b, y, delta)
        if x[0] != y[0] or (x[0] == 'decnz' and x[1] != y[1]):
            return False, len(seen), (a, x, b, y)
        if x[0] == 'decnz':
            todo.append((x[2], y[2], ())); todo.append((x[3], y[3], ()))
    return True, len(seen), maxdelta

if __name__ == '__main__':
    ok, n, info = bisim_commuting(mine, e1, theirs, e2)
    print('bisimilar up to commuting increments:', ok, 'states', n, 'max pending delta / info:', info)
