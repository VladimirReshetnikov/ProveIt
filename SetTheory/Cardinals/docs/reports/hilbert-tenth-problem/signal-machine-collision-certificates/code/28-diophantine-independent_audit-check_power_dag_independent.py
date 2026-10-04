#!/usr/bin/env python3
"""Independent inert-JSON POWER equation audit; no author code is imported."""
import hashlib
import json
from collections import Counter
from functools import lru_cache
from pathlib import Path

ROOT = Path('/workspace/shared/five-signal-diophantine58-20261004')
OUT = Path('/workspace/shared/five-signal-certificate58-independent-audit-20261004')


class P:
    def __init__(self, terms):
        self.terms = {m: c for m, c in terms.items() if c}

    @classmethod
    def lift(cls, p):
        return p if isinstance(p, cls) else cls({(): p})

    def __add__(self, other):
        terms = dict(self.terms)
        for m, c in self.lift(other).terms.items():
            terms[m] = terms.get(m, 0) + c
        return P(terms)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) - self

    def __mul__(self, other):
        terms = {}
        for m, c in self.terms.items():
            for n, d in self.lift(other).terms.items():
                mn = tuple(sorted(m + n))
                terms[mn] = terms.get(mn, 0) + c * d
        return P(terms)

    __rmul__ = __mul__

    def square(self):
        return self * self


def var(name):
    return P({(name,): 1})


def audit():
    raw = (ROOT / 'evidence/three-input-linear.dag.json').read_bytes()
    data = json.loads(raw)
    gates = data['gates']
    witnesses = data['witnesses']
    assert len(witnesses) == len(set(witnesses))
    equations = {name: (left, right) for name, left, right in data['equations']}
    assert len(equations) == len(data['equations'])

    @lru_cache(None)
    def polynomial(ref):
        kind, rest = ref.split(':', 1)
        if kind == 'c':
            return P.lift(int(rest))
        if kind == 'w':
            assert rest in witnesses
            return var(rest)
        if kind == 'i':
            assert rest in data['inputs']
            return var('INPUT.' + rest)
        assert kind == 'g'
        i = int(rest)
        op, lhs, rhs = gates[i]
        for arg in (lhs, rhs):
            if arg.startswith('g:'):
                assert int(arg[2:]) < i
        a, b = polynomial(lhs), polynomial(rhs)
        assert op in ('+', '-', '*')
        return a + b if op == '+' else a - b if op == '-' else a * b

    def closure(refs, stops=frozenset()):
        seen = set()
        stack = list(refs)
        while stack:
            ref = stack.pop()
            if ref in seen or ref in stops:
                continue
            seen.add(ref)
            if ref.startswith('g:'):
                stack.extend(gates[int(ref[2:])][1:])
        return seen

    natural = ['dwb', 'dwk', 'dyk', 'alpha1', 'alpha2', 'sigma1', 'sigma2',
               'tau1', 'tau2', 'rho1', 'rho2']
    positive = ['out', 'w', 'M', 'g', 'x', 'y', 'u', 'v', 's', 't', 'qb', 'qv', 'strict']
    report = {'input_sha256': hashlib.sha256(raw).hexdigest(), 'modules': []}
    exponent = var('valuation.n.Plus') - 1
    assert polynomial('g:36').terms == exponent.terms
    bases = [('power5', P.lift(5), 'c:5'),
             ('power_complex', 3 + 4 * (4 * var('power5.out') + 1), 'g:115')]
    for name, base, base_ref in bases:
        leaf = lambda suffix: var(name + '.' + suffix)
        p = {s: leaf(s) for s in positive}
        n = {s: leaf(s + '.Plus') - 1 for s in natural}
        expected_leaves = set(name + '.' + s for s in positive + ['aMinus1', 'betaMinus1'])
        expected_leaves.update(name + '.' + s + '.Plus' for s in natural)
        actual_leaves = {w for w in witnesses if w.startswith(name + '.')}
        assert actual_leaves == expected_leaves
        assert len(actual_leaves) == 26
        a, beta = leaf('aMinus1') + 1, leaf('betaMinus1') + 1
        k, m = exponent + 1, base * p['out']
        w, M, g, x, y, u, v, s, t, qb, qv, Jp = [p[z] for z in positive[1:]]
        expected = [
            (x.square(), 1 + (a.square() - 1) * y.square()),
            (u.square(), 1 + (a.square() - 1) * v.square()),
            (s.square(), 1 + (beta.square() - 1) * t.square()),
            (beta, 1 + 4 * y * qb),
            (beta + u * n['alpha1'], a + u * n['alpha2']),
            (v, y.square() * qv),
            (s + u * n['sigma1'], x + u * n['sigma2']),
            (t + 4 * y * n['tau1'], k + 4 * y * n['tau2']),
            (y, k + n['dyk']),
            (w, base + n['dwb']),
            (w, k + n['dwk']),
            (M, m + Jp),
            (a.square(), 1 + ((w + 1).square() - 1) * (w * g).square()),
            (2 * a * base, M + (base.square() + 1)),
            (x + M * n['rho1'], y * (a - base) + m + M * n['rho2']),
        ]
        assert polynomial(base_ref).terms == base.terms
        expected_labels = {name + '.eq' + str(i) for i in range(1, 16)}
        assert {q for q in equations if q.startswith(name + '.')} == expected_labels
        eq_reports = []
        refs = []
        for index, (left, right) in enumerate(expected, 1):
            label = name + '.eq' + str(index)
            lhs, rhs = equations[label]
            assert polynomial(lhs).terms == left.terms, (label, 'left')
            assert polynomial(rhs).terms == right.terms, (label, 'right')
            residual = left - right
            eq_reports.append({'equation': index, 'left': lhs, 'right': rhs,
                               'exact_sides_match': True,
                               'residual_degree': max(map(len, residual.terms)),
                               'residual_monomials': len(residual.terms)})
            refs.extend((lhs, rhs))
        inside = closure(refs, frozenset([base_ref, 'g:36']))
        indices = sorted(int(r[2:]) for r in inside if r.startswith('g:'))
        ops = Counter(gates[i][0] for i in indices)
        assert ops == {'*': 31, '+': 24, '-': 15}
        used = {r[2:] for r in inside if r.startswith('w:')}
        assert used == expected_leaves
        assert len(indices) == 70
        report['modules'].append({'name': name, 'leaf_count': len(actual_leaves),
                                  'equation_count': len(eq_reports),
                                  'body_gate_count': len(indices), 'operations': dict(ops),
                                  'body_gate_indices': indices, 'equations': eq_reports})
    return report


if __name__ == '__main__':
    result = audit()
    text = json.dumps(result, indent=2) + '\n'
    (OUT / 'POWER_DAG_RECEIPT.json').write_text(text)
    print(text)
