#!/usr/bin/env python3
"""Independent exact audit of the compact twelve-variable circuit.

The checks prove a universal polynomial identity for the final norm kernel,
audit the complete literal gate list and a uniform leading coefficient,
and check signed full-circuit substitutions. They do not verify the imported
Pell/compiler theorem or decide the existence of a zero.

Python 3 standard library only. Usage:
  python3 verify_compact12.py PATH_TO_CIRCUIT_DIRECTORY
The directory must contain compact12_system.json, compact12_product.json,
and compact12_sos.json. The script prints a JSON audit receipt.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json
import random
import sys


def require(value, message):
    if not value:
        raise ValueError(message)


class Poly:
    """An exact sparse polynomial over Z in a fixed list of generators."""
    count = 0

    def __init__(self, terms=None):
        self.terms = {m: c for m, c in (terms or {}).items() if c}

    @classmethod
    def integer(cls, n):
        return cls({(0,) * cls.count: n})

    @classmethod
    def variable(cls, index):
        powers = [0] * cls.count
        powers[index] = 1
        return cls({tuple(powers): 1})

    @classmethod
    def coerce(cls, value):
        return value if isinstance(value, cls) else cls.integer(value)

    def __add__(self, other):
        other = self.coerce(other)
        terms = dict(self.terms)
        for monomial, coefficient in other.terms.items():
            terms[monomial] = terms.get(monomial, 0) + coefficient
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        terms = {}
        for left, a in self.terms.items():
            for right, b in other.terms.items():
                monomial = tuple(x + y for x, y in zip(left, right))
                terms[monomial] = terms.get(monomial, 0) + a * b
        return Poly(terms)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        result = Poly.integer(1)
        base = self
        while exponent:
            if exponent & 1:
                result = result * base
            base = base * base
            exponent //= 2
        return result

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms


def evaluate(packet, supplied):
    values = dict(supplied)
    for name, operator, left, right in packet['source']:
        a = left if isinstance(left, int) else values[left]
        b = right if isinstance(right, int) else values[right]
        values[name] = a + b if operator == '+' else a - b if operator == '-' else a * b
    return values


def kernel_identity(packet):
    """Full symbolic comparison, not a finite evaluation check.

    The independent side multiplies four quartic factors in the ring
    Z[H,L,A,e,S,G,d,P,U,B][u,t]/(u^2-G,t^2-A), where Jtau=4B.
    Coefficient comparison verifies the kernel for every integer choice.
    """
    names = ['H', 'L', 'A', 'e', 'S', 'G', 'd', 'P', 'U', 'HBnd']
    Poly.count = len(names)
    v = {name: Poly.variable(j) for j, name in enumerate(names)}
    original = dict(v)
    start = next(j for j, row in enumerate(packet['source']) if row[0] == 'H2')
    for name, operator, left, right in packet['source'][start:]:
        a = Poly.integer(left) if isinstance(left, int) else v[left]
        b = Poly.integer(right) if isinstance(right, int) else v[right]
        v[name] = a + b if operator == '+' else a - b if operator == '-' else a * b
        if name == 'N':
            break
    z = Poly.integer(0)
    one = Poly.integer(1)
    A, G = original['A'], original['G']

    def multiply(left, right):
        out = [z, z, z, z]
        for j, a in enumerate(left):
            for k, b in enumerate(right):
                coefficient = a * b
                if j & k & 1:
                    coefficient = coefficient * G
                if j & k & 2:
                    coefficient = coefficient * A
                out[j ^ k] = out[j ^ k] + coefficient
        return out

    accumulator = [one, z, z, z]
    for sign_u, sign_t in product((-1, 1), repeat=2):
        linear = [original['S'], -sign_u * original['L'], -sign_t * 4 * original['HBnd'], z]
        square = multiply(linear, linear)
        inner = [original['d'] * a for a in square]
        inner[0] = inner[0] - original['H'] ** 2 * original['e']
        quartic = multiply(inner, inner)
        quartic[0] = quartic[0] - 4 * original['H'] ** 4 * original['P'] * original['U']
        accumulator = multiply(accumulator, quartic)
    require(all(a == 0 for a in accumulator[1:]), 'Formal conjugate product did not descend')
    require(accumulator[0] == v['N'], 'Universal norm-kernel identity failed')
    serial = json.dumps(sorted((list(m), c) for m, c in v['N'].terms.items()), separators=(',', ':'))
    return {'status': 'PASS', 'formal_parameters': names,
            'expanded_norm_monomials': len(v['N'].terms),
            'expanded_norm_sha256': hashlib.sha256(serial.encode()).hexdigest(),
            'method': 'Complete sparse-polynomial coefficient comparison with four conjugate quartic factors'}


def ledger(packet):
    available = set(packet['witnesses'] + packet['fixed_numerals'])
    degrees = {v: 1 for v in packet['witnesses']}
    degrees.update({v: 0 for v in packet['fixed_numerals']})
    for name, op, left, right in packet['source']:
        require(name not in available, 'Duplicate circuit register: ' + name)
        require(op in '+-*', 'Unexpected operation')
        require(all(isinstance(v, int) or v in available for v in (left, right)), 'Undefined circuit input')
        a = 0 if isinstance(left, int) else degrees[left]
        b = 0 if isinstance(right, int) else degrees[right]
        degrees[name] = a + b if op == '*' else max(a, b)
        available.add(name)
    outputs = [packet['output']] if 'output' in packet else [v for pair in packet['comparisons'] for v in pair if isinstance(v, str)]
    live = set(outputs)
    for name, _, left, right in reversed(packet['source']):
        require(name in live, 'Dead circuit register: ' + name)
        live.update(v for v in (left, right) if isinstance(v, str))
    require(set(packet['witnesses'] + packet['fixed_numerals']) <= live, 'Unused supplied input')
    counts = Counter(row[1] for row in packet['source'])
    return {'operations': len(packet['source']), 'multiplications': counts['*'],
            'additions_subtractions': counts['+'] + counts['-'],
            'degree_upper_bounds': {v: degrees[v] for v in outputs},
            'all_inputs_and_registers_live': True}


def leading_form_audit(packet):
    """Exact universal leading form with beta fixed symbolically.

    Only the highest homogeneous components are retained. These are enough
    because all relevant highest components are explicitly nonzero; if a
    cancellation occurred, the verification would reject it.
    """
    names = list(packet['witnesses']) + list(packet['fixed_numerals'])
    Poly.count = len(names)
    values = {name: (1, Poly.variable(j)) for j, name in enumerate(packet['witnesses'])}
    for j, name in enumerate(packet['fixed_numerals'], start=len(packet['witnesses'])):
        values[name] = (0, Poly.variable(j))
    for name, operator, left, right in packet['source']:
        da, a = (0, Poly.integer(left)) if isinstance(left, int) else values[left]
        db, b = (0, Poly.integer(right)) if isinstance(right, int) else values[right]
        if operator == '*':
            degree, top = da + db, a * b
        else:
            degree = max(da, db)
            aa = a if da == degree else Poly.integer(0)
            bb = b if db == degree else Poly.integer(0)
            top = aa + bb if operator == '+' else aa - bb
        require(top != 0, 'Highest-degree cancellation at ' + name)
        values[name] = (degree, top)
    vars = {name: Poly.variable(j) for j, name in enumerate(names)}
    q0 = vars['beta'] * vars['J']
    k0 = vars['eta'] + vars['zeta']
    predicted = (2 ** 32 * vars['i'] ** 48 * k0 ** 96 * vars['w'] ** 80 *
                 vars['s'] ** 176 * q0 ** 656 * (q0 - vars['F']) ** 16)
    require(values['N'][0] == 1072, 'Norm degree is not 1072')
    require(values['N'][1] == predicted, 'Uniform leading-form coefficient identity failed')
    require(values['Nk'][1] == -vars['h'] * vars['w'] * vars['s'] * q0 ** 4, 'Index leading form failed')
    require(values['Nt'][1] == vars['w'] * (q0 - vars['F'] - vars['alpha']) - vars['z'] * q0,
            'Transport leading form failed')
    return {'status': 'PASS', 'norm_degree': 1072, 'product_degree': 1081,
            'sum_of_squares_degree': 2144, 'norm_leading_monomials': len(predicted.terms),
            'uniformity': 'Every beta>0; the other three coefficient ports do not occur in the highest form'}


def signed_checks(system, product_packet, sos):
    rng = random.Random(0xC0121081)
    cases = 48
    for case in range(cases):
        supplied = {name: rng.randrange(-4, 5) for name in system['witnesses'] + system['fixed_numerals']}
        if case >= cases // 2:
            supplied = {name: Fraction(v, rng.randrange(1, 4)) for name, v in supplied.items()}
        value = evaluate(system, supplied)
        q = supplied['beta'] * supplied['J'] + 1
        X, Y = supplied['w'] * q, supplied['s'] * q ** 3
        E = X * Y
        k = supplied['eta'] + supplied['zeta']
        c = k * Y + supplied['eta']
        a = E + Y
        H = 4 * a + 3
        Delta = a * a + H
        ell = E * k * Y
        R = ((q - 1) * (q - supplied['F']) + supplied['alpha']) * (q * q - 1) + (supplied['MC'] + q * supplied['MF']) * supplied['J']
        I = supplied['i'] * c * c
        D = 1 + Delta * I * I
        Q = (Delta * I) ** 2
        v, b = c * supplied['T'], c + R * D
        W = supplied['T'] ** 2 + X * I * I
        direct = dict(q=q, X=X, Y=Y, E=E, k=k, c=c, a=a, H=H, Delta=Delta,
                      A=1 + ell * (ell + k), G=1 + Delta * c * c,
                      R=R, Nk=k - supplied['h'] * E - R,
                      Nt=(supplied['K0'] + supplied['w']) * (q - supplied['F'] - supplied['alpha']) + q - supplied['F'] - supplied['z'] * (q - 1),
                      I=I, I2=I * I, D=D, Q=Q, d=Q - 1,
                      v2=v * v, b=b, e=Q * (D * v * v + b * b) - 1,
                      Bnd=W, L=1 + H * W, taucoef=4 * H * W,
                      S=X + a * c + H * supplied['r'])
        require(all(value[name] == result for name, result in direct.items()), 'Independent core-formula transcription failed')
        require(evaluate(product_packet, supplied)['polynomial'] == value['Nk'] * value['Nt'] * (1 + value['N']) - 1,
                'Product finalizer identity failed')
        require(evaluate(sos, supplied)['sos'] == (value['Nk'] - 1) ** 2 + (value['Nt'] - 1) ** 2 + value['N'] ** 2,
                'Sum-of-squares finalizer identity failed')
        require(value['I2'] == supplied['i'] ** 2 * value['c'] ** 4, 'I-square block failed')
        require(value['Q'] == (value['Delta'] * value['I']) ** 2, 'Q-square identity failed')
        require(value['Bnd'] == supplied['T'] ** 2 + value['X'] * value['I2'], 'New weight failed')
        require(value['taucoef'] == 4 * value['H'] * value['Bnd'], 'Tau coefficient failed')
        if case < cases // 2:
            require(value['N1'] % 8 == 0, 'Parity divisibility failed')
            require(value['N'] % 4 != 2, 'Product parity guard failed')
    return {'status': 'PASS', 'exact_signed_integer_cases': cases // 2, 'exact_signed_rational_cases': cases // 2}


def main():
    directory = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parents[1] / 'circuits'
    packets = [json.loads((directory / ('compact12_' + kind + '.json')).read_text()) for kind in ['system', 'product', 'sos']]
    expected_product_tail = [['guard', '+', 1, 'N'], ['KN', '*', 'Nk', 'Nt'],
                             ['prod', '*', 'KN', 'guard'], ['polynomial', '-', 'prod', 1]]
    expected_sos_tail = [['rk', '-', 'Nk', 1], ['rksq', '*', 'rk', 'rk'],
                         ['rt', '-', 'Nt', 1], ['rtsq', '*', 'rt', 'rt'],
                         ['Nsq', '*', 'N', 'N'], ['sos0', '+', 'rksq', 'rtsq'],
                         ['sos', '+', 'sos0', 'Nsq']]
    require(packets[1]['source'] == packets[0]['source'] + expected_product_tail, 'Product is not exactly the asserted universal finalizer')
    require(packets[2]['source'] == packets[0]['source'] + expected_sos_tail, 'Sum of squares is not exactly the asserted universal finalizer')
    audit = {'scope': 'Independent polynomial and circuit audit, not an end-to-end formal compiler proof',
             'circuit_ledgers': [ledger(packet) for packet in packets]}
    require([x['operations'] for x in audit['circuit_ledgers']] == [112, 116, 119], 'Unexpected operation counts')
    audit['universal_norm_identity'] = kernel_identity(packets[0])
    audit['universal_leading_form'] = leading_form_audit(packets[0])
    audit['signed_evaluations'] = signed_checks(*packets)
    audit['status'] = 'PASS'
    print(json.dumps(audit, indent=2))


if __name__ == '__main__':
    main()
