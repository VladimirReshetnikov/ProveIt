#!/usr/bin/env python3
"""Exact sparse-polynomial emitter for the proof's degree-two sign compiler.

New self-contained arithmetic code. No machine simulation or upstream imports.
Writes only three named files below its supplied output directory.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path


def require(p, message):
    if not p:
        raise RuntimeError(message)


def add(*polys):
    out = {}
    for p in polys:
        for monomial, coefficient in p.items():
            out[monomial] = out.get(monomial, 0) + coefficient
    return {m: c for m, c in out.items() if c}


def scale(p, coefficient):
    return {m: coefficient*c for m, c in p.items() if coefficient*c}


def mul(p, q):
    out = {}
    for a, ca in p.items():
        for b, cb in q.items():
            m = tuple(sorted(a+b))
            out[m] = out.get(m, 0) + ca*cb
    return {m: c for m, c in out.items() if c}


ONE = {(): 1}


def var(name):
    return {(name,): 1}


def sub(p, q):
    return add(p, scale(q, -1))


def evaluate(p, values):
    total = 0
    for m, c in p.items():
        term = c
        for name in m:
            term *= values[name]
        total += term
    return total


def encoded(p):
    return [{'coefficient': c, 'monomial': list(m)} for m, c in sorted(p.items())]


class Compiler:
    def __init__(self, inputs, atoms):
        self.inputs = tuple(inputs)
        self.atoms = atoms
        self.witnesses = []
        self.residuals = []
        self.gates = []
        self.flags = {}
        self.interned = {}
        for name, q in atoms.items():
            require(all(len(m) <= 2 for m in q), 'atom degree exceeds two')
            en, ez, ep, zz = (self.new(name+'_'+s) for s in ('negative', 'zero', 'positive', 'magnitude'))
            self.flags[name] = (en, ez, ep, zz)
            for e in (en, ez, ep):
                self.residuals.append(mul(var(e), sub(var(e), ONE)))
            self.residuals.append(sub(add(var(en), var(ez), var(ep)), ONE))
            self.residuals.append(sub(q, mul(sub(var(ep), var(en)), add(var(zz), ONE))))
            self.residuals.append(mul(var(ez), var(zz)))

    def new(self, name):
        require(name not in self.inputs and name not in self.witnesses, 'duplicate variable')
        self.witnesses.append(name)
        return name

    def expression(self, node):
        node = tuple(node)
        if node in self.interned:
            return self.interned[node]
        op = node[0]
        if op == 'sign':
            name, sense = node[1], node[2]
            ix = {'negative': 0, 'zero': 1, 'positive': 2}[sense]
            result = self.flags[name][ix]
        else:
            child_names = tuple(self.expression(child) for child in node[1:])
            require(op in ('and', 'or', 'not'), 'unknown connective')
            require(len(child_names) == (1 if op == 'not' else 2), 'gate arity')
            result = self.new('gate_'+str(len(self.gates)))
            u = var(child_names[0])
            if op == 'not':
                target = sub(ONE, u)
            else:
                v = var(child_names[1])
                target = mul(u, v) if op == 'and' else sub(add(u, v), mul(u, v))
            self.residuals.append(sub(var(result), target))
            self.gates.append((result, op, child_names))
        self.interned[node] = result
        return result

    def finish(self, formula):
        self.output = self.expression(formula)
        self.residuals.append(sub(var(self.output), ONE))
        self.polynomial = add(*(mul(r, r) for r in self.residuals))
        require(all(len(m) <= 2 for r in self.residuals for m in r), 'residual degree')
        require(all(len(m) <= 4 for m in self.polynomial), 'polynomial degree')
        live = {v for m in self.polynomial for v in m}
        require(set(self.inputs+self.witnesses_tuple()) <= live, 'dead variable')
        require(len(self.witnesses) == 4*len(self.atoms)+len(self.gates), 'witness ledger')
        require(len(self.residuals) == 6*len(self.atoms)+len(self.gates)+1, 'residual ledger')

    def witnesses_tuple(self):
        return tuple(self.witnesses)

    def canonical(self, inputs):
        require(set(inputs) == set(self.inputs), 'input key mismatch')
        require(all(type(x) is int and x >= 0 for x in inputs.values()), 'input domain')
        values = dict(inputs)
        for name, q in self.atoms.items():
            n = evaluate(q, values)
            en, ez, ep, zz = self.flags[name]
            values.update({en: int(n < 0), ez: int(n == 0), ep: int(n > 0), zz: max(abs(n)-1, 0)})
        for name, op, args in self.gates:
            u = values[args[0]]
            if op == 'not':
                values[name] = 1-u
            elif op == 'and':
                values[name] = u*values[args[1]]
            else:
                v = values[args[1]]
                values[name] = u+v-u*v
        return values

    def export(self, title, predicate, formula):
        return {'title': title, 'predicate': predicate, 'domain': 'all inputs and witnesses are natural integers',
                'inputs': list(self.inputs), 'witnesses': self.witnesses,
                'atoms': {name: encoded(q) for name, q in self.atoms.items()},
                'formula': formula, 'logic_gates': self.gates,
                'residuals': [encoded(r) for r in self.residuals],
                'expanded_polynomial': encoded(self.polynomial),
                'ledger': {'atoms': len(self.atoms), 'logic_gates': len(self.gates),
                           'witnesses': len(self.witnesses), 'residuals': len(self.residuals),
                           'degree': max(map(len, self.polynomial)), 'monomials': len(self.polynomial)}}


def positive(name):
    return ('sign', name, 'positive')


def nonnegative(name):
    return ('not', ('sign', name, 'negative'))


def probe(compiler, expected):
    accepted = rejected = mutations = expansion_cases = 0
    for x, y in itertools.product(range(13), repeat=2):
        values = compiler.canonical(dict(zip(compiler.inputs, (x, y))))
        claim = expected(x, y)
        residual_total = sum(evaluate(r, values)**2 for r in compiler.residuals)
        polynomial_total = evaluate(compiler.polynomial, values)
        require(polynomial_total == residual_total, 'expanded versus SOS mismatch')
        require((polynomial_total == 0) == claim, 'predicate mismatch')
        require(polynomial_total == (0 if claim else 1), 'canonical rejection value')
        expansion_cases += 1
        if claim:
            accepted += 1
            for name in compiler.witnesses:
                for change in (-1, 1, 2):
                    if values[name]+change < 0:
                        continue
                    altered = dict(values)
                    altered[name] += change
                    s = sum(evaluate(r, altered)**2 for r in compiler.residuals)
                    p = evaluate(compiler.polynomial, altered)
                    require(p == s and p > 0, 'witness mutation accepted')
                    mutations += 1
                    expansion_cases += 1
        else:
            rejected += 1
    # Arbitrary off-graph tuples exercise complete polynomial equality.
    names = compiler.inputs+compiler.witnesses_tuple()
    for n in range(250):
        values = {name: (n*n+3*n*i+7*i*i) % 11 for i, name in enumerate(names)}
        require(evaluate(compiler.polynomial, values) ==
                sum(evaluate(r, values)**2 for r in compiler.residuals), 'off-graph identity')
        expansion_cases += 1
    return {'accepted_inputs': accepted, 'rejected_inputs': rejected,
            'single_witness_mutations_rejected': mutations, 'expanded_SOS_comparisons': expansion_cases}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', required=True)
    args = parser.parse_args()
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)
    d, y = var('d'), var('y')
    atoms1 = {'gap': d, 'limit_margin': sub(scale(y, 2), d)}
    formula1 = ('and', positive('gap'), nonnegative('limit_margin'))
    c1 = Compiler(('d', 'y'), atoms1)
    c1.finish(formula1)
    export1 = c1.export('Four-signal infinite collision macro',
                        'd>0 and 2y>=d; the exact infinite-validity set of PROOF.md Section 7', formula1)
    x, y = var('x'), var('y')
    # Exact infinite first-coordinate positivity for B=((2,-1),(-1,1)).
    # Its positive eigenvalues are (3 +/- sqrt(5))/2. This is an arithmetic
    # recurrence diagnostic, not claimed to be a complete physical macro.
    c = sub(x, scale(y, 2))
    hh = scale(sub(add(mul(x, x), mul(x, y)), mul(y, y)), 4)
    atoms2 = {'x': x, 'C': c, 'H': hh}
    formula2 = ('and', positive('x'),
                ('or', nonnegative('C'),
                 ('and', ('sign', 'C', 'negative'), nonnegative('H'))))
    c2 = Compiler(('x', 'y'), atoms2)
    c2.finish(formula2)
    export2 = c2.export('Nonsquare-spectrum sign compiler diagnostic',
                        'For all n>=0, first coordinate of [[2,-1],[-1,1]]^n (x,y) is positive; recurrence diagnostic only', formula2)
    tests1 = probe(c1, lambda d, y: d > 0 and 2*y >= d)
    tests2 = probe(c2, lambda x, y: x > 0 and x*x+x*y-y*y >= 0)
    files = {}
    for filename, data in (('four_signal_quartic.json', export1), ('quadratic_sign_quartic.json', export2)):
        payload = (json.dumps(data, indent=2, sort_keys=True)+'\n').encode()
        (out/filename).write_bytes(payload)
        files[filename] = {'sha256': hashlib.sha256(payload).hexdigest(), 'bytes': len(payload), **data['ledger']}
    receipt = {'status': 'PASS', 'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'files': files, 'checks': {'four_signal': tests1, 'quadratic_diagnostic': tests2},
               'scope': 'literal sign-formula compiler; no general machine/macro parser or physical simulator',
               'uniqueness': 'proved algebraically in PROOF.md; finite mutations are regression evidence'}
    payload = (json.dumps(receipt, indent=2, sort_keys=True)+'\n').encode()
    (out/'sign_compiler_receipt.json').write_bytes(payload)
    print(payload.decode(), end='')


if __name__ == '__main__':
    main()
