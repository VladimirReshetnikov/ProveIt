#!/usr/bin/env python3
"""A finite K/S/MP certificate for exchange of two curried premises.

This verifies a proof in the free implicational algebra. The PA machine's
unchanged dominated implication basis supplies K and S; this script does not
replace that separate basis derivation or a proof assistant kernel.
"""
from pathlib import Path
import argparse
import hashlib
import json

def arrow(a, b): return ('imp', a, b)
P, Q, R = ('atom', 'P'), ('atom', 'Q'), ('atom', 'R')

def variable(name, typ): return ('var', name, typ)
def k(a, b): return ('K', a, b)
def s(a, b, c): return ('S', a, b, c)

def typ(t):
    if t[0] == 'var': return t[2]
    if t[0] == 'K': return arrow(t[1], arrow(t[2], t[1]))
    if t[0] == 'S':
        _, a, b, c = t
        return arrow(arrow(a, arrow(b, c)), arrow(arrow(a, b), arrow(a, c)))
    if t[0] == 'app':
        f, x = typ(t[1]), typ(t[2])
        assert f[0] == 'imp' and f[1] == x, (f, x)
        return f[2]
    raise ValueError(t)

def app(f, x):
    t = ('app', f, x)
    typ(t)
    return t

def occurs(name, t):
    if t[0] == 'var': return t[1] == name
    if t[0] == 'app': return occurs(name, t[1]) or occurs(name, t[2])
    return False

def identity(a):
    return app(app(s(a, arrow(a, a), a), k(a, arrow(a, a))), k(a, a))

def abstract(name, a, t):
    if t[0] == 'var' and t[1] == name:
        assert t[2] == a
        return identity(a)
    if not occurs(name, t): return app(k(typ(t), a), t)
    assert t[0] == 'app'
    f, x = t[1:]
    return app(app(s(a, typ(x), typ(t)), abstract(name, a, f)), abstract(name, a, x))

def make_certificate():
    f = variable('f', arrow(P, arrow(Q, R)))
    p, q = variable('p', P), variable('q', Q)
    body = app(app(f, p), q)
    term = abstract('f', typ(f), abstract('q', Q, abstract('p', P, body)))
    expected = arrow(arrow(P, arrow(Q, R)), arrow(Q, arrow(P, R)))
    assert typ(term) == expected
    nodes, ids = [], {}
    def record(t):
        if t in ids: return ids[t]
        if t[0] == 'app':
            row = dict(rule='MP', implication=record(t[1]), argument=record(t[2]))
        else:
            assert t[0] in ('K', 'S'), 'Undischarged hypothesis'
            row = dict(rule=t[0], parameters=t[1:])
        row['conclusion'] = typ(t)
        index = len(nodes)
        ids[t] = index
        nodes.append(row)
        return index
    final = record(term)
    return dict(format='finite-K-S-MP-1', atoms=['P', 'Q', 'R'], nodes=nodes,
                final=final, theorem=expected)

def freeze(x): return tuple(map(freeze, x)) if isinstance(x, list) else x

def verify(certificate):
    """Check just the published DAG, independently of bracket abstraction."""
    assert certificate['format'] == 'finite-K-S-MP-1'
    conclusions = []
    for i, row in enumerate(certificate['nodes']):
        rule = row['rule']
        if rule == 'K':
            a, b = map(freeze, row['parameters'])
            conclusion = arrow(a, arrow(b, a))
        elif rule == 'S':
            a, b, c = map(freeze, row['parameters'])
            conclusion = arrow(arrow(a, arrow(b, c)), arrow(arrow(a, b), arrow(a, c)))
        elif rule == 'MP':
            f, x = row['implication'], row['argument']
            assert 0 <= f < i and 0 <= x < i
            major, minor = conclusions[f], conclusions[x]
            assert major[0] == 'imp' and major[1] == minor
            conclusion = major[2]
        else: raise ValueError(rule)
        assert conclusion == freeze(row['conclusion'])
        conclusions.append(conclusion)
    expected = arrow(arrow(P, arrow(Q, R)), arrow(Q, arrow(P, R)))
    assert conclusions[certificate['final']] == freeze(certificate['theorem']) == expected
    return dict(status='PASS', nodes=len(conclusions),
                K=sum(r['rule'] == 'K' for r in certificate['nodes']),
                S=sum(r['rule'] == 'S' for r in certificate['nodes']),
                MP=sum(r['rule'] == 'MP' for r in certificate['nodes']),
                hypotheses=0, theorem='(P -> (Q -> R)) -> (Q -> (P -> R))',
                scope='Universal finite proof template over arbitrary formula codes, using K/S/MP.')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    cert = make_certificate()
    data = (json.dumps(cert, indent=2) + '\n').encode()
    # Serialization/reload separates construction from certificate replay.
    receipt = verify(json.loads(data))
    receipt['certificate_sha256'] = hashlib.sha256(data).hexdigest()
    (args.output / 'exchange_certificate.json').write_bytes(data)
    (args.output / 'exchange_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__': main()
