"""Exact Python mirror of RM.v path semantics on inductive trees, and the bisimulation certificate
between two programs (used to generate the Coq certificate; the Coq checker re-verifies everything).

tree: ('N', t0, t1) | ('L', edge);  edge = ('inc', r) | ('dec', r) | ('brk', k) | ('cont', k) | ('halt',)
"""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__))
INPUTS = os.path.normpath(os.path.join(HERE, '..', '..', 'inputs'))
REGS = ['nextproof', 'topwff', 'wffstack', 'axiomcode', 'param1', 'param2', 'scratch1', 'scratch2', 'prooflist']
RIDX = {r: i for i, r in enumerate(REGS)}

def parse_op(o):
    if o == 'halt':
        return ('halt',)
    if o.startswith('_break.'):
        return ('brk', int(o.split('.')[1]))
    if o.startswith('_continue.'):
        return ('cont', int(o.split('.')[1]))
    _, r, k = o.split('.')
    return ('inc' if k == 'inc' else 'dec', RIDX[r])

def tree_of_paths(paths):
    root = {}
    for p, o in paths:
        assert p.startswith('110')
        p = p[3:]                  # paths.json carries the 3-cell marker prefix '110'
        cur = root
        for c in p[:-1]:
            cur = cur.setdefault(c, {})
        assert p[-1] not in cur
        cur[p[-1]] = ('L', parse_op(o))
    def conv(d):
        if isinstance(d, tuple):
            return d
        assert set(d) == {'0', '1'}, d.keys()
        return ('N', conv(d['0']), conv(d['1']))
    return conv(root)

def load_p254():
    return tree_of_paths(json.load(open(os.path.join(INPUTS, 'paths.json'))))

def dag_edge(e):
    k = e[0]
    if k == 'op':
        return ('inc' if e[2] == 'inc' else 'dec', RIDX[e[1]])
    if k == 'break':
        return ('brk', e[1])
    if k == 'continue':
        return ('cont', e[1])
    if k == 'halt':
        return ('halt',)
    raise ValueError(e)

def tree_of_dag(nodes, root='main().0'):
    memo = {}
    def conv(n):
        if n not in memo:
            a, b = nodes[n]
            memo[n] = ('N', sub(a), sub(b))
        return memo[n]
    def sub(e):
        return conv(e[1]) if e[0] == 'node' else ('L', dag_edge(e))
    return conv(root)

def bit(P, i):
    return P[i] if i < len(P) else False

def walk(t, P):
    i = 0
    while True:
        assert t[0] == 'N'
        c = t[2] if bit(P, i) else t[1]
        i += 1
        if c[0] == 'L':
            return c[1], i
        t = c

def site(t, P):
    e, d = walk(t, P)
    return e, (list(P) + [False] * d)[:d]

def inc_path(Q):
    l = list(reversed(Q)); out = []
    i = 0
    while i < len(l) and l[i]:
        out.append(False); i += 1
    if i < len(l):
        out.append(True); out += l[i + 1:]
    return list(reversed(out))

def strip_path(b, k, Q):
    l = list(reversed(Q))
    while k > 0 and l:
        x = l.pop(0)
        if x == b:
            k -= 1
    return list(reversed(l))

def brk(k, Q):
    return inc_path(strip_path(False, k, Q))

def cont(k, Q):
    return strip_path(True, k, Q)

def seg(t, P, fuel=100000):
    """run inc / break / continue leaves; returns (list of incremented regs, path at the next test)."""
    incs = []
    for _ in range(fuel):
        e, Q = site(t, P)
        if e[0] == 'inc':
            incs.append(e[1]); P = inc_path(Q)
        elif e[0] == 'brk':
            P = brk(e[1], Q)
        elif e[0] == 'cont':
            P = cont(e[1], Q)
        else:
            return incs, P
    raise RuntimeError('seg fuel')

def counts(l):
    return tuple(l.count(r) for r in range(len(REGS)))

def certificate(t1, t2):
    """list of (P1, P2, nz_index, z_index); entry 0 = start pair."""
    l1, P1 = seg(t1, []); l2, P2 = seg(t2, [])
    assert counts(l1) == counts(l2)
    key = lambda a, b: (tuple(a), tuple(b))
    idx = {key(P1, P2): 0}; ents = [[P1, P2, None, None]]; todo = [0]
    def get(a, b):
        k = key(a, b)
        if k not in idx:
            idx[k] = len(ents); ents.append([a, b, None, None]); todo.append(idx[k])
        return idx[k]
    while todo:
        i = todo.pop()
        P1, P2 = ents[i][0], ents[i][1]
        e1, Q1 = site(t1, P1); e2, Q2 = site(t2, P2)
        if e1 == ('halt',) and e2 == ('halt',):
            continue
        assert e1[0] == 'dec' and e1 == e2, (i, e1, e2)
        for slot, (A, B) in ((2, (inc_path(Q1), inc_path(Q2))), (3, (brk(1, Q1), brk(1, Q2)))):
            la, Pa = seg(t1, A); lb, Pb = seg(t2, B)
            assert counts(la) == counts(lb), (i, la, lb)
            ents[i][slot] = get(Pa, Pb)
    return ents

if __name__ == '__main__':
    sys.path.insert(0, os.path.normpath(os.path.join(HERE, '..', '..', 'logic')))
    from build_dag import load_dag
    nodes, regidx = load_dag()
    assert [r for r, _ in sorted(regidx.items(), key=lambda x: x[1])] == REGS
    t1 = load_p254(); t2 = tree_of_dag(nodes)
    ents = certificate(t1, t2)
    print('certificate entries', len(ents))
    print('max path lengths', max(len(e[0]) for e in ents), max(len(e[1]) for e in ents))
    import collections
    print('p254 tests related to >1 dag path:', sum(1 for v in collections.Counter(tuple(e[0]) for e in ents).values() if v > 1))
