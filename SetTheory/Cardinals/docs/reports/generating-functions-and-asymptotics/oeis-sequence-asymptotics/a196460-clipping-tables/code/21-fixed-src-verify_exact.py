"""Fresh exact arithmetic checks, independent of all author/upstream code.

Uses Python's standard library only. Outputs new evidence; reads no project inputs.
Sparse Laurent polynomials have exponents (s, h, t), with h = 1/log(2).
"""
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import json

ORDER = 6

def mono(c=1, s=0, h=0, t=0):
    return {(s, h, t): Q(c)} if c else {}

def add(*ps):
    out = {}
    for p in ps:
        for e, c in p.items():
            out[e] = out.get(e, Q(0)) + c
    return {e: c for e, c in out.items() if c}

def mul(p, q):
    out = {}
    for e, c in p.items():
        for f, d in q.items():
            g = tuple(a + b for a, b in zip(e, f))
            if g[2] <= ORDER:
                out[g] = out.get(g, Q(0)) + c * d
    return {e: c for e, c in out.items() if c}

def power(p, k):
    out = mono()
    for _ in range(k):
        out = mul(out, p)
    return out

def scale(p, c=1, s=0, h=0, t=0):
    return mul(p, mono(c, s, h, t))

def coefficient(p, k):
    return {(s, h, 0): c for (s, h, t), c in p.items() if t == k}

def binpoly(k):
    out = mono()
    for j in range(k):
        out = mul(out, add(mono(s=1), mono(-j)))
    return scale(out, Q(1, factorial(k)))

def evaluate(p, x):
    assert all(h == t == 0 for s, h, t in p)
    return sum(c * Q(x)**s for (s, h, t), c in p.items())

def substitute(poly, delta):
    out = {}
    for (s, h, t), c in poly.items():
        assert h == t == 0 and s >= 0
        out = add(out, scale(power(add(mono(s=1), delta), s), c))
    return out

def exponential(poly):
    assert all(t >= 1 for s, h, t in poly)
    out = mono()
    for j in range(1, ORDER + 1):
        out = add(out, scale(power(poly, j), Q(1, factorial(j))))
    return out

def residual(delta, logs):
    out = add(scale(delta, 2, s=1), mul(delta, delta))
    for k in range(1, ORDER + 1):
        out = add(out, scale(mul(substitute(logs[k], delta),
                        exponential(scale(delta, -k, h=-1))), h=1, t=k))
    return out

def terms(poly):
    return [{'s': s, 'h': h, 't': t, 'coefficient': str(c)}
            for (s, h, t), c in sorted(poly.items(), reverse=True)]

def a_single(n):
    return sum(comb(n, k) * (1 + 2**k)**n for k in range(n + 1))

def a_double(n):
    return sum(comb(n, r) * comb(n, c) * 2**((n-r)*(n-c))
               for r in range(n + 1) for c in range(n + 1))

def sector_value(n, k):
    return sum(comb(n, r) * comb(n, k-r) * 2**(r*(k-r))
               for r in range(max(0, k-n), min(n, k) + 1))

def graph_sum(n):
    out = 0
    for graph in range(1 << (n*n)):
        left = sum(not any(graph & (1 << (i*n+j)) for j in range(n))
                   for i in range(n))
        right = sum(not any(graph & (1 << (i*n+j)) for i in range(n))
                    for j in range(n))
        out += 1 << (left + right)
    return out

def closed_count(k):
    out = 0
    full = (1 << (k*k)) - 1
    corner = 1 << (k*k - 1)
    rows = [sum(1 << (i*k+j) for j in range(k)) for i in range(k-1)]
    columns = [sum(1 << (i*k+j) for i in range(k)) for j in range(k-1)]
    for table in range(1 << (k*k)):
        if table & corner:
            out += table == full
            continue
        if any(table & (1 << (i*k+k-1)) and table & row != row
               for i, row in enumerate(rows)):
            continue
        if any(table & (1 << ((k-1)*k+j)) and table & col != col
               for j, col in enumerate(columns)):
            continue
        out += 1
    return out

def main():
    ps = [sum_polys(scale(mul(binpoly(r), binpoly(k-r)), 2**(r*(k-r)))
                    for r in range(k+1)) for k in range(ORDER+1)]
    logs = [{}]
    for k in range(1, ORDER+1):
        logs.append(add(ps[k], sum_polys(scale(mul(logs[j], ps[k-j]), -Q(j, k))
                                        for j in range(1, k))))
    ds = [{}]
    delta = {}
    for k in range(1, ORDER+1):
        d = scale(coefficient(residual(delta, logs), k), -Q(1, 2), s=-1)
        ds.append(d)
        delta = add(delta, scale(d, t=k))
        assert not coefficient(residual(delta, logs), k)
    assert residual(delta, logs) == {}
    assert ds[1] == mono(-1, h=1)
    assert ds[2] == add(mono(-Q(1, 2), s=1, h=1), mono(-Q(1, 2), h=1),
                        mono(Q(1, 2), s=-1, h=2))
    assert all(max(e[0] for e in ds[k]) <= k-1 for k in range(1, ORDER+1))
    exact = []
    for n in range(33):
        a = a_single(n)
        assert a == a_double(n)
        assert Q(a, 2**(n*n)) == sum(Q(sector_value(n, k), 2**(k*n))
                                    for k in range(2*n+1))
        assert 2**(n*n) <= a <= 2**(n*n+2*n) < 2**((n+1)**2)
        if n >= 1:
            assert 2**(n*n) < a+1 < 2**((n+1)**2)
        for k in range(ORDER+1):
            assert evaluate(ps[k], n) == sector_value(n, k)
        exact.append({'n': n, 'a_n': str(a), 'C_n': str(a+1)})
    closure = [{'K': k, 'count': closed_count(k)} for k in range(1, 5)]
    assert [v['count'] for v in closure] == [2, 6, 48, 1194]
    graphs = [{'n': n, 'weighted_count': graph_sum(n)} for n in range(5)]
    assert all(v['weighted_count'] == a_single(v['n']) for v in graphs)
    evidence = {'checks': {'exact_sequences': 33, 'polynomial_values': 33*(ORDER+1),
                'closure_tables': sum(2**(k*k) for k in range(1, 5)),
                'graphs': sum(2**(n*n) for n in range(5)),
                'formal_inverse_order': ORDER, 'formal_residual_zero': True},
                'initial_terms': exact, 'closure': closure, 'graphs': graphs,
                'P': [terms(p) for p in ps], 'L': [terms(p) for p in logs],
                'D': [terms(p) for p in ds], 'conventions': {'h': '1/ln(2)',
                's': 'sqrt(log_2(y))', 't': '2^(-s)'}}
    output = Path(__file__).parent / 'evidence' / 'exact.json'
    with output.open('x') as stream:
        json.dump(evidence, stream, indent=2)
        stream.write('\n')
    print(json.dumps(evidence['checks'], sort_keys=True))
    for name, polys in [('P', ps), ('L', logs), ('D', ds)]:
        for k, poly in enumerate(polys[:5]):
            print(name, k, terms(poly))

def sum_polys(items):
    out = {}
    for p in items:
        out = add(out, p)
    return out

if __name__ == '__main__':
    main()
