"""Independent sparse-polynomial ledger for the binary prism template."""
from itertools import combinations_with_replacement
from collections import defaultdict, Counter
from audit_independent import prism

def plus(*ps):
    o = defaultdict(int)
    for p in ps:
        for m, c in p.items():
            o[m] += c
    return {m: c for m, c in o.items() if c}

def scale(p, c):
    return {m: c * a for m, a in p.items() if c * a}

def mul(p, q):
    o = defaultdict(int)
    for m, a in p.items():
        for n, b in q.items():
            o[tuple(sorted(m + n))] += a * b
    return {m: c for m, c in o.items() if c}

def square(p):
    return mul(p, p)

def const(c):
    return {(): c} if c else {}

def var(x):
    return {(x,): 1}

def sub(p, q):
    return plus(p, scale(q, -1))

def lin(*pairs):
    return plus(*(scale(var(v), a) for v, a in pairs))

def build(shape, eta, background=0):
    vs, ns, halo = prism(shape)
    eta = tuple(eta)
    if not len(eta) == len(vs):
        raise AssertionError('audit check failed at source line 26')
    edges = [(i, j) for i in range(len(vs)) for j in ns[i] if i < j]

    def v(i, t):
        return var(f'{i}:{t}')
    ranks = [plus(v(i, 'k'), scale(v(i, 'c'), 2), v(i, 'beta')) for i in range(len(vs))]
    us = [plus(v(i, 'k'), v(i, 'c')) for i in range(len(vs))]
    As = [{} for _ in vs]
    Bs = [{} for _ in vs]
    edge_terms = []
    for i, j in edges:
        lm, ln, l0, lp, lplus = (var(f'{i},{j}:{s}') for s in ('lm', 'ln', 'l0', 'lp', 'lplus'))
        sig = var(f'{i},{j}:sig')
        delta = sub(ranks[j], ranks[i])
        As[i] = plus(As[i], l0, lp, lplus)
        Bs[i] = plus(Bs[i], ln, l0, lp, lplus)
        As[j] = plus(As[j], lm, ln, l0)
        Bs[j] = plus(Bs[j], lm, ln, l0, lp)
        edge_terms.extend([square(plus(lm, ln, l0, lp, lplus, const(-1))), mul(lm, square(plus(delta, const(2), sig))), mul(ln, square(plus(delta, const(1)))), mul(l0, square(delta)), mul(lp, square(plus(delta, const(-1)))), mul(lplus, square(plus(delta, const(-2), scale(sig, -1)))), mul(plus(ln, l0, lp), sig)])
    vertex_terms = []
    vertex_raw = []
    for i in range(len(vs)):
        z, ell, f, k, c, beta, g, h = (v(i, t) for t in ('z', 'ell', 'f', 'k', 'c', 'beta', 'g', 'h'))
        ts = [square(plus(z, scale(us[i], 6), *(scale(us[j], -1) for j in ns[i]), const(-eta[i]))), square(plus(z, ell, const(-5))), square(plus(f, k, c, const(-1))), mul(plus(f, k), beta), mul(us[i], square(plus(z, scale(As[i], -1), scale(g, -1)))), mul(f, g), mul(c, square(plus(Bs[i], scale(z, -1), const(-1), scale(h, -1)))), mul(plus(f, k), h)]
        d = len(ns[i])
        q = 3 + 2 * d + bool(eta[i])
        expected = q * (q + 1) // 2 + 21 + (2 + 3 * d) * (3 + 3 * d) + (4 * d + 3) * (4 * d + 4) // 2
        if not sum(map(len, ts)) == expected:
            raise AssertionError('audit check failed at source line 56')
        vertex_terms.extend(ts)
        vertex_raw.append(expected)
    halo_terms = []
    for x in sorted(halo):
        neighbors = [i for i, y in enumerate(vs) if sum((abs(a - b) for a, b in zip(x, y))) == 1]
        halo_terms.append(square(plus(*(us[i] for i in neighbors), var(f'H{x}'), const(background - 5))))
    terms = vertex_terms + edge_terms + halo_terms
    p = plus(*terms)
    if not len(terms) == 8 * len(vs) + 7 * len(edges) + len(halo):
        raise AssertionError('audit check failed at source line 63')
    variables = {x for m in p for x in m}
    if not len(variables) == 8 * len(vs) + 6 * len(edges) + len(halo):
        raise AssertionError('audit check failed at source line 65')
    if not sum(map(len, edge_terms)) == 173 * len(edges):
        raise AssertionError('audit check failed at source line 66')
    return {'shape': shape, 'initial_heights': eta, 'background': background, 'variables': len(variables), 'summands': len(terms), 'raw_monomials': sum(map(len, terms)), 'collected_monomials': len(p), 'degree_profile': dict(sorted(Counter(map(len, p)).items())), 'vertex_raw': vertex_raw, 'polynomial': p, 'terms': terms}

def evaluate(p, values):
    out = 0
    for m, a in p.items():
        for x in m:
            a *= values[x]
        out += a
    return out
if __name__ == '__main__':
    import json
    ledger = []
    for shape, eta, bg in [((1, 1, 1), (0,), 0), ((1, 1, 1), (1,), 0), ((1, 1, 1), (6,), 0), ((1, 1, 1), (6,), 5), ((2, 1, 1), (5, 5), 0), ((2, 1, 1), (6, 5), 0), ((2, 2, 1), (6, 5, 4, 0), 0), ((2, 2, 2), (6, 5, 4, 3, 2, 1, 0, 0), 0)]:
        d = build(shape, eta, bg)
        d.pop('polynomial')
        d.pop('terms')
        ledger.append(d)
    print(json.dumps(ledger, indent=2))
