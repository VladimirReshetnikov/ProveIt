#!/usr/bin/env python3
"""Check the emitted ordinary-strong circuits and quadratic33 packet.

This is exact arithmetic and syntax verification, not a proof of compiler
semantics or a search for a complete Diophantine witness.
"""
from __future__ import annotations

import ast
from collections import Counter
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[1] / 'data'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def circuit_check(packet):
    known = set(packet['witnesses'] + packet['fixed_numerals'])
    producers = {}
    for name, op, a, b in packet['source']:
        require(name not in known and op in ('+', '-', '*'), 'bad gate')
        for x in (a, b):
            require(type(x) is int or x in known, 'bad input')
        known.add(name)
        producers[name] = (a, b)
    outputs = ([packet['output']] if 'output' in packet else
               [x for row in packet['comparisons'] for x in row
                if isinstance(x, str)])
    needed = set(outputs)
    for name, _, a, b in reversed(packet['source']):
        if name in needed:
            needed.update(x for x in (a, b) if isinstance(x, str))
    require(set(producers) <= needed, 'dead gate')
    require(set(packet['witnesses'] + packet['fixed_numerals']) <= needed,
            'dead port')
    counts = Counter(row[1] for row in packet['source'])
    ledger = dict(operations=len(packet['source']), M=counts['*'],
                  A=counts['+'] + counts['-'])
    require(ledger == packet['ledger'], 'bad ledger')
    rng = random.Random(1045)
    degrees = []
    for _ in range(3):
        vals = {n: [rng.randrange(1, 17), rng.randrange(1, 17)]
                for n in packet['witnesses']}
        vals.update({n: [v] for n, v in
                     zip(packet['fixed_numerals'], [31, 127, 10, 45])})

        def get(x):
            return [x] if type(x) is int else vals[x]

        def add(a, b, sign=1):
            c = [(a[i] if i < len(a) else 0) +
                 sign * (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))]
            while len(c) > 1 and c[-1] == 0:
                c.pop()
            return c

        for name, op, a, b in packet['source']:
            aa, bb = get(a), get(b)
            if op == '*':
                c = [0] * (len(aa) + len(bb) - 1)
                for i, x in enumerate(aa):
                    for j, y in enumerate(bb):
                        c[i + j] += x * y
                while len(c) > 1 and c[-1] == 0:
                    c.pop()
            else:
                c = add(aa, bb, 1 if op == '+' else -1)
            vals[name] = c
        if 'output' in packet:
            degree = len(vals[packet['output']]) - 1
            require(degree == packet['exact_degree'], 'degree diagnostic')
        else:
            degree = [len(add(get(a), get(b), -1)) - 1
                      for a, b in packet['comparisons']]
            require(degree == packet['residual_exact_degrees'],
                    'residual degree diagnostic')
        degrees.append(degree)
    return {'ledger': ledger, 'all_gates_and_ports_live': True,
            'exact_integer_affine_line_degrees': degrees}


class Sparse:
    """Small exact commutative polynomial ring with named indeterminates."""
    def __init__(self, names):
        self.names = names
        self.index = {n: i for i, n in enumerate(names)}
        self.zero = (0,) * len(names)

    def const(self, n):
        return {self.zero: n} if n else {}

    def var(self, n):
        require(n in self.index, 'undeclared indeterminate')
        e = list(self.zero)
        e[self.index[n]] = 1
        return {tuple(e): 1}

    def add(self, a, b, sign=1):
        r = a.copy()
        for e, c in b.items():
            r[e] = r.get(e, 0) + sign * c
            if not r[e]:
                del r[e]
        return r

    def mul(self, a, b):
        r = {}
        for e, c in a.items():
            for f, d in b.items():
                ef = tuple(x + y for x, y in zip(e, f))
                r[ef] = r.get(ef, 0) + c * d
        return {e: c for e, c in r.items() if c}

    def parse(self, text):
        def walk(n):
            if isinstance(n, ast.Constant) and type(n.value) is int:
                return self.const(n.value)
            if isinstance(n, ast.Name):
                return self.var(n.id)
            if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub):
                return {e: -c for e, c in walk(n.operand).items()}
            if isinstance(n, ast.BinOp):
                a = walk(n.left)
                if isinstance(n.op, ast.Pow):
                    require(isinstance(n.right, ast.Constant) and
                            type(n.right.value) is int and
                            0 <= n.right.value <= 4, 'unsupported exponent')
                    r = self.const(1)
                    for _ in range(n.right.value):
                        r = self.mul(r, a)
                    return r
                b = walk(n.right)
                if isinstance(n.op, ast.Add):
                    return self.add(a, b)
                if isinstance(n.op, ast.Sub):
                    return self.add(a, b, -1)
                if isinstance(n.op, ast.Mult):
                    return self.mul(a, b)
            raise ValueError('unsupported polynomial syntax')
        return walk(ast.parse(text.strip(), mode='eval').body)


def quadratic_check(d):
    require(len(d['variables']) == d['variable_count'] == 33,
            'quadratic witness count')
    require(len(d['equations_factored']) == d['equation_count'] == 24,
            'quadratic equation count')
    ring = Sparse(d['variables'] + d['fixed_numerals'])
    residuals = []
    for eq, expanded in zip(d['equations_factored'], d['residual_polynomials']):
        lhs, rhs = eq.split('=')
        r = ring.add(ring.parse(lhs), ring.parse(rhs), -1)
        require(r == ring.parse(expanded), 'expanded residual mismatch')
        require(max(sum(e[:33]) for e in r) <= 2, 'nonquadratic residual')
        residuals.append(r)
    sos = {}
    for r in residuals:
        sos = ring.add(sos, ring.mul(r, r))
    require(max(sum(e[:33]) for e in sos) == 4, 'quartic degree')
    monomial = list(ring.zero)
    monomial[ring.index['tau_root']] = 4
    require(sos[tuple(monomial)] == 1, 'tau^4 coefficient')
    return {'variables': 33, 'equations': 24,
            'all_factored_equations_match_expansions': True,
            'all_residuals_quadratic': True, 'sum_of_squares_exact_degree': 4,
            'coefficient_of_tau_fourth_power': 1}


def main():
    report = {}
    for name in ['blank_ordinary_system61.json', 'blank_ordinary_poly69.json',
                 'blank_ordinary_sos78.json']:
        report[name] = circuit_check(json.loads((ROOT / name).read_text()))
    name = 'blank_ordinary_quartic33.json'
    report[name] = quadratic_check(json.loads((ROOT / name).read_text()))
    report['scope'] = ('Exact gate and polynomial audits. Degree diagnostics '
                       'supplement the uniform leading-form proof. No complete '
                       'machine coefficient or halting witness is materialized.')
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
