#!/usr/bin/env python3
"""Exact sparse identities, circuit integrity, and homogeneous-degree certificates.

Standard library only. Run from any directory; Python -O is supported.
This is a finite algebra audit, not a proof assistant or a consistency test.
"""
import hashlib
import json
from collections import Counter
from pathlib import Path
import build

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Ring:
    def __init__(self, names):
        self.names = list(names)
        self.zero_monomial = (0,) * len(names)

    def scalar(self, value):
        return Poly(self, {self.zero_monomial: value} if value else {})

    def var(self, name):
        exp = list(self.zero_monomial)
        exp[self.names.index(name)] = 1
        return Poly(self, {tuple(exp): 1})


class Poly:
    def __init__(self, ring, terms):
        self.ring = ring
        self.terms = {m: c for m, c in terms.items() if c}

    def coerce(self, other):
        return other if isinstance(other, Poly) else self.ring.scalar(other)

    def __add__(self, other):
        other = self.coerce(other)
        out = self.terms.copy()
        for m, c in other.terms.items():
            out[m] = out.get(m, 0) + c
        return Poly(self.ring, out)

    __radd__ = __add__

    def __neg__(self):
        return Poly(self.ring, {m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        out = {}
        for a, c in self.terms.items():
            for b, d in other.terms.items():
                m = tuple(x + y for x, y in zip(a, b))
                out[m] = out.get(m, 0) + c * d
        return Poly(self.ring, out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, 'Non-polynomial power')
        result = self.ring.scalar(1)
        value = self
        while exponent:
            if exponent & 1:
                result = result * value
            exponent //= 2
            if exponent:
                value = value * value
        return result

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms


def local_identities():
    ring = Ring(['q', 'ell', 'r', 'Y', 'k', 'a', 'c', 'X', 'H', 'gamma',
                 'V', 'u', 'U', 'f', 'index'])
    q, ell, r, Y, k, a, c, X, H, gamma, V, u, U, f, index = map(ring.var, ring.names)
    lhs = (q**3*(ell+r)+Y)**2-q**6*(ell*(ell+k)+1)
    rhs = q**6*(r*r+ell*(2*r-k)-1)+2*q**3*(ell+r)*Y+Y*Y
    require(lhs == rhs, 'First-carrier cancellation failed')
    Z = X+gamma*H
    D = a*c+Z
    Delta = a*a+H
    main = 2*a*c*Z+Z*Z-H*c*c
    require(D*D-Delta*c*c == main, 'Main-norm cancellation failed')
    require((q*D+X*H)**2-q*q*(Delta*c*c+1)
            == q*q*(main-1)+2*q*D*X*H+(X*H)**2,
            'Main-carrier cancellation failed')
    def aux(value):
        return (value+u)**2-U*u*(2*value+u)-1
    require(aux(V) == U*(V*V-(V+u)**2)+(V+u)**2-1,
            'Auxiliary root-gap identity failed')
    require(aux(V+f*f*index)-aux(V)
            == f*f*index*(2*(V+u)+f*f*index-2*U*u),
            'Index-ideal reduction identity failed')
    return 5


def validate_graph(packet):
    available = set(packet['witnesses'] + packet['fixed_numerals'])
    require(len(packet['witnesses']) == 15, 'Wrong witness count')
    require(len(available) == 19, 'Duplicate/missing inputs')
    for row in packet['source']:
        require(len(row) == 4, 'Malformed gate')
        name, op, x, y = row
        require(name not in available, 'Duplicate gate')
        require(op in ('+', '-', '*'), 'Uncharged operator')
        require(all(isinstance(a, int) or a in available for a in (x, y)),
                'Forward or undefined reference')
        available.add(name)
    require(packet['output'] in available, 'Missing output')
    needed = {packet['output']}
    for name, op, x, y in reversed(packet['source']):
        if name in needed:
            needed.update((x, y))
    require(all(r[0] in needed for r in packet['source']), 'Dead gate')
    require(set(packet['witnesses']+packet['fixed_numerals']) <= needed, 'Dead input')
    require(len(packet['source']) == packet['operations'], 'Incorrect operation count')
    require(dict(Counter(r[1] for r in packet['source'])) == packet['operation_breakdown'],
            'Incorrect operation breakdown')


def top_forms(packet):
    """Propagate exact top forms through the cancellation-expanded certificate.

    A coefficient port has witness-degree zero. If leading forms cancel
    completely, fail rather than silently making a degree claim. The two
    explicit identities above remove precisely the problematic gates.
    """
    names = packet['witnesses'] + packet['fixed_numerals']
    ring = Ring(names)
    env = {n: (1 if n in packet['witnesses'] else 0, ring.var(n)) for n in names}
    def get(value):
        return (0, ring.scalar(value)) if isinstance(value, int) else env[value]
    for name, op, x, y in packet['source']:
        dx, px = get(x)
        dy, py = get(y)
        if op == '*':
            degree, poly = dx+dy, px*py
        elif dx > dy:
            degree, poly = dx, px
        elif dy > dx:
            degree, poly = dy, -py if op == '-' else py
        else:
            degree, poly = dx, px-py if op == '-' else px+py
        require(bool(poly.terms), 'Uncertified complete leading cancellation at '+name)
        env[name] = degree, poly
    return ring, env


def expected_leader(degree, ring):
    v = {n: ring.var(n) for n in ring.names}
    k, Y, f, u = v['eta']+v['zeta'], v['Y'], v['f'], v['u']
    if degree in (24, 26):
        X, q0 = v['X'], 3*v['beta']*v['j']
    else:
        q0 = v['beta']*v['J']
        X = v['w']*q0
    if degree == 24:
        return 4*X**4*Y**6*f**8*u**2*(k*v['T']+v['h']*X)**2
    R0 = q0**3*(q0-v['F'])
    aux = 2*X**2*Y**2*f**4*u*R0
    if degree == 26:
        return aux**2
    n1 = 8*v['gamma']*X**2*Y**3*k
    nk = -v['h']*X*Y-R0
    nt = v['w']*(q0-v['F']-v['alpha'])-v['z']*q0
    return (n1*nk*nt)**2+aux**2


def serialized_poly(poly):
    return [{'coefficient': c,
             'powers': {n: e for n, e in zip(poly.ring.names, m) if e}}
            for m, c in sorted(poly.terms.items())]


def main():
    identity_count = local_identities()
    results = []
    expected_residual_degrees = {24: [11, 9, 4, 3, 12, 10],
                                 26: [11, 9, 7, 13, 10],
                                 30: [12, 15, 15, 10]}
    expected_operations = {24: 90, 26: 88, 30: 79}
    for degree in (24, 26, 30):
        for certificate in (False, True):
            suffix = '_degree_certificate' if certificate else ''
            path = ROOT/'circuits'/('p15_degree'+str(degree)+suffix+'.json')
            packet = json.loads(path.read_text())
            require(packet == build.build(degree, certificate), 'Generator mismatch: '+path.name)
            validate_graph(packet)
            if not certificate:
                require(packet['operations'] == expected_operations[degree], 'Unexpected evaluator size')
                primary_sha = hashlib.sha256(path.read_bytes()).hexdigest()
                continue
            ring, env = top_forms(packet)
            residual_degrees = [env[r][0] for r in packet['residuals']]
            require(residual_degrees == expected_residual_degrees[degree], 'Residual degree mismatch')
            got_degree, got_leader = env[packet['output']]
            require(got_degree == degree, 'Final degree mismatch')
            require(got_leader == expected_leader(degree, ring), 'Leading homogeneous form mismatch')
            # These coefficients survive the actual specialization beta>0.
            if degree == 24:
                powers, coeff = {'X': 6, 'Y': 6, 'f': 8, 'u': 2, 'h': 2}, 4
            elif degree == 26:
                powers, coeff = {'X': 4, 'Y': 4, 'f': 8, 'u': 2, 'j': 6, 'F': 2, 'beta': 6}, 4*3**6
            else:
                powers, coeff = {'w': 4, 'J': 10, 'Y': 4, 'f': 8, 'u': 2, 'F': 2, 'beta': 10}, 4
            monomial = tuple(powers.get(n, 0) for n in ring.names)
            require(got_leader.terms.get(monomial) == coeff, 'Specialization certificate failed')
            results.append({'degree': degree, 'witnesses': 15,
                            'operations': expected_operations[degree],
                            'primary_circuit_sha256': primary_sha,
                            'certificate_circuit_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                            'residual_degrees': residual_degrees,
                            'leading_form': serialized_poly(got_leader),
                            'nonzero_coefficient': {'powers': powers, 'coefficient': coeff}})
    ledger = json.loads((ROOT/'PROVENANCE.json').read_text())
    for row in ledger['files']:
        require(hashlib.sha256((ROOT/row['path']).read_bytes()).hexdigest() == row['sha256'],
                'Upstream file changed: '+row['path'])
    receipt = {'status': 'PASS', 'scope': 'Finite exact algebra and literal circuit audit; not a proof assistant.',
               'exact_local_polynomial_identities': identity_count,
               'authenticated_upstream_files': len(ledger['files']), 'circuits': results}
    target = ROOT/'certificates'/'EXACT_ALGEBRA.json'
    target.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'status': 'PASS', 'exact_identities': identity_count,
                      'degrees': [r['degree'] for r in results],
                      'operations': [r['operations'] for r in results],
                      'authenticated_upstream_files': len(ledger['files'])}, indent=2))


if __name__ == '__main__':
    main()
