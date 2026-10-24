#!/usr/bin/env python3
"""Exact compositional polynomial audit against the numerical C222 definitions.

Every rewrite replaces a sparse polynomial by a named wire only after exact
coefficient equality with that wire's defining polynomial. No random testing
or large-degree expansion is used for the axiom-code comparison.
"""
import json
from collections import defaultdict
from hashlib import sha256
from pathlib import Path


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def key(p):
    return tuple(sorted((m, c) for m, c in p.items() if c))


class Ring:
    def __init__(self, definitions):
        self.rules = {}
        self.matches = set()
        for w in definitions:
            p = defaultdict(int)
            for t in w['value']:
                p[tuple(sorted(t['monomial']))] += t['coefficient']
            self.rules[key(p)] = w['name']

    def simplify(self, p):
        canonical = key(p)
        if canonical in self.rules:
            name = self.rules[canonical]
            self.matches.add(name)
            return {(name,): 1}
        return dict(canonical)

    def constant(self, value):
        return {(): value} if value else {}

    def var(self, name):
        return {(name,): 1}

    def add(self, x, y):
        out = defaultdict(int, x)
        for m, c in y.items():
            out[m] += c
        return self.simplify(out)

    def mul(self, x, y):
        out = defaultdict(int)
        for mx, cx in x.items():
            for my, cy in y.items():
                out[tuple(sorted(mx + my))] += cx * cy
        return self.simplify(out)

    def scale(self, c, p):
        return self.mul(self.constant(c), p)


def source_polynomial(rows):
    out = defaultdict(int)
    for r in rows:
        out[tuple(sorted(r['monomial']))] += r['coefficient']
    return dict(key(out))


def verify_branch(branch):
    ring = Ring(branch['definitions'])
    a, b, c, d, p, q, v = [ring.var(s) for s in ['a','b','c','d','p','q','v']]
    one, two, three = [ring.constant(n) for n in [1,2,3]]
    add, mul = ring.add, ring.mul
    def I(x, y):
        s = add(x, y)
        return add(ring.scale(2, mul(s, add(s, one))), ring.scale(4, y))
    def A(x, y): return add(I(x, y), two)
    def M(x, y): return add(I(x, y), one)
    def E(x, y): return add(I(x, y), three)
    def N(x): return I(x, one)
    def X(x, y): return N(A(x, N(y)))
    def req(x, k, matrix):
        return A(x, I(matrix, N(A(x, I(matrix, N(M(x, k)))))))
    def clos(x, y, k, matrix):
        subset = A(k, I(M(k,x), M(k,y)))
        tail = I(subset, req(y,k,matrix))
        tail = N(A(x,tail))
        tail = N(A(x,I(matrix,tail)))
        return A(y,I(M(y,k),tail))
    def bundle(x, y, z):
        nks = A(z,I(clos(x,y,z,z), N(req(y,z,z))))
        vrel = I(M(x,y),A(z,M(x,y)))
        return N(I(vrel,nks))

    name = branch['name']
    if name == 'truth':
        expected = [p,q,v]
    elif name == 'mp':
        expected = [add(q,ring.scale(-1,I(p,v)))]
    else:
        if name == 'rho1': code = X(a,E(a,b))
        elif name == 'rho2': code = I(A(a,I(b,c)),I(A(a,b),A(a,c)))
        elif name == 'rho3': code = I(E(a,b),I(M(c,a),M(c,b)))
        elif name == 'rho4': code = I(A(a,A(b,c)),A(b,A(a,c)))
        elif name == 'rho5': code = I(E(c,a),I(M(c,b),M(a,b)))
        elif name == 'rho6': code = I(X(a,A(a,b)),b)
        elif name == 'growG': code = I(E(c,a),I(E(c,b),A(M(a,b),E(a,b))))
        elif name == 'rho8': code = I(I(I(c,d),a),I(I(a,c),I(b,c)))
        elif name == 'bundle': code = bundle(a,b,c)
        elif name == 'gen': code = A(a,p)
        else: raise RuntimeError('unknown branch')
        endpoint = add(v,ring.scale(-1,code))
        expected = [q,endpoint] if name == 'gen' else [p,q,endpoint]
        if name == 'bundle':
            ca = add(c,ring.scale(-1,a)); cb = add(c,ring.scale(-1,b))
            dp = add(d,one)
            guard = add(mul(mul(ca,ca),mul(cb,cb)),ring.scale(-1,mul(dp,dp)))
            expected.insert(0,guard)
    require(len(expected) == len(branch['residuals']), 'residual count: '+name)
    for i, (actual, target) in enumerate(zip(branch['residuals'], expected)):
        require(source_polynomial(actual) == target, 'exact code identity: '+name+' row '+str(i))
    require(ring.matches == {w['name'] for w in branch['definitions']},
            'some source wire was not recognized compositionally: '+name+' '+str(ring.matches))
    return dict(branch=name, exact_row_identities=len(expected), wire_definition_rewrites=len(ring.matches))


def main():
    here = Path(__file__).resolve().parent
    source_path = here/'wire_eliminated_source.json'
    source = json.loads(source_path.read_text())
    result = dict(status='PASS', method='exact sparse-polynomial rewriting against literal C222 code definitions',
                  source_sha256=sha256(source_path.read_bytes()).hexdigest(),
                  branches=[verify_branch(b) for b in source['horn_branches']],
                  definition_sources=['Code254.lean', 'KCode222.lean'],
                  scope='Exact local numerical-code equality; inherited semantic C222-to-ZFC calibration is separate.')
    (here/'CALCULUS_AUDIT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    main()
