#!/usr/bin/env python3
"""Audit the literal P69 DAG and its exact degree using only the standard library.

The sole cancellation requiring more than leading-term arithmetic is the main
Pell norm. Its polynomial identity is checked exactly in independent cut
variables, then used to establish its bound and leading homogeneous form.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
DIRECTORY = ROOT / 'Computability/DiophantineConsistency/circuits'
CIRCUIT = DIRECTORY / 'p69_unscaled.json'
LEDGER = DIRECTORY / 'p69_unscaled.audit.json'


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Ring:
    """Sparse integer polynomials; tuple exponents avoid symbolic dependencies."""
    def __init__(self, names):
        self.names = tuple(names)
        self.zero = (0,) * len(names)

    def constant(self, value):
        return {self.zero: value} if value else {}

    def variable(self, name):
        degree = list(self.zero)
        degree[self.names.index(name)] = 1
        return {tuple(degree): 1}

    @staticmethod
    def add(left, right):
        result = dict(left)
        for exponent, coefficient in right.items():
            result[exponent] = result.get(exponent, 0) + coefficient
            if result[exponent] == 0:
                del result[exponent]
        return result

    def neg(self, value):
        return {exponent: -coefficient for exponent, coefficient in value.items()}

    def sub(self, left, right):
        return self.add(left, self.neg(right))

    @staticmethod
    def mul(left, right):
        result = {}
        for a, c in left.items():
            for b, d in right.items():
                exponent = tuple(x + y for x, y in zip(a, b))
                result[exponent] = result.get(exponent, 0) + c * d
        return {exponent: coefficient for exponent, coefficient in result.items() if coefficient}

    def power(self, value, exponent):
        result = self.constant(1)
        for _ in range(exponent):
            result = self.mul(result, value)
        return result


def main_norm_identity():
    ring = Ring(['a', 'c', 'X', 'g', 'H'])
    a, c, x, g, h = map(ring.variable, ring.names)
    add, sub, mul, sq = ring.add, ring.sub, ring.mul, lambda p: ring.power(p, 2)
    ac = mul(a, c)
    source = sub(sq(add(add(ac, x), g)), mul(add(sq(a), h), sq(c)))
    expanded = sub(add(add(sq(x), mul(ring.constant(2), mul(ac, add(x, g)))),
                       add(mul(ring.constant(2), mul(x, g)), sq(g))), mul(h, sq(c)))
    require(source == expanded, 'main norm identity failed')
    # Source degrees: a=6,c=5,X=2,g=7,H=6. Only 2acg has degree18.
    weights = [6, 5, 2, 7, 6]
    degrees = {exponent: sum(x * y for x, y in zip(exponent, weights))
               for exponent in expanded}
    require(max(degrees.values()) == 18, 'main norm bound failed')
    top = {exponent: coefficient for exponent, coefficient in expanded.items()
           if degrees[exponent] == 18}
    require(top == mul(ring.constant(2), mul(ac, g)), 'main norm leader failed')
    return dict(identity='(ac+X+g)^2-(a^2+H)c^2 = X^2+2ac(X+g)+2Xg+g^2-Hc^2',
                cut_degrees=dict(zip(ring.names, weights)), degree=18,
                cut_leading_form='2*a*c*g')


def audit(circuit):
    witnesses, constants, gates = (circuit[key] for key in ('witnesses', 'fixed_numerals', 'source'))
    require(len(witnesses) == 15 and len(set(witnesses)) == 15, 'expected 15 distinct witnesses')
    require(len(constants) == 4 and len(set(constants)) == 4, 'expected four distinct ports')
    require(not set(witnesses).intersection(constants), 'overlapping ports')
    names = witnesses + constants
    ring = Ring(names)
    producers = {}
    known = set(names)
    counts = {'+': 0, '-': 0, '*': 0}
    leading = {name: (1 if name in witnesses else 0, ring.variable(name)) for name in names}
    main_identity = main_norm_identity()
    main_shapes = {
        'cam2': ('*', 'R10a', 'R12'),
        'D1': ('+', 'wn2', 'cam2'),
        'gam': ('*', 'gamma', 'a4m5'),
        'R14': ('+', 'D1', 'gam'),
        'L15': ('*', 'R14', 'R14'),
        'a_square': ('*', 'R12', 'R12'),
        'A': ('+', 'a_square', 'a4m5'),
        'c2': ('*', 'R10a', 'R10a'),
        'Ac2': ('*', 'A', 'c2'),
        'a4': ('*', 4, 'R12'),
        'a4m5': ('+', 'a4', 3),
    }
    for name, operation, left, right in gates:
        if name in main_shapes:
            require((operation, left, right) == main_shapes[name], 'changed main identity producer: ' + name)

    def value(operand):
        if type(operand) is int:
            return 0, ring.constant(operand)
        require(type(operand) is str and operand in known, 'unavailable or invalid operand: ' + str(operand))
        return leading[operand]

    for gate in gates:
        require(type(gate) is list and len(gate) == 4, 'invalid gate')
        name, operation, left, right = gate
        require(type(name) is str and name not in known, 'duplicate output: ' + str(name))
        require(operation in counts, 'invalid operation')
        ld, lp = value(left)
        rd, rp = value(right)
        if operation == '*':
            degree, polynomial = ld + rd, ring.mul(lp, rp)
        else:
            degree = max(ld, rd)
            a, b = (lp if ld == degree else {}), (rp if rd == degree else {})
            polynomial = ring.add(a, b) if operation == '+' else ring.sub(a, b)
        if name == 'norm_main':
            require((operation, left, right) == ('-', 'L15', 'Ac2'), 'changed main norm cuts')
            # All-value identity verified above; g=gamma*(4a+3), whose leader is 4*gamma*a.
            a = leading['R12'][1]
            c = leading['R10a'][1]
            polynomial = ring.mul(ring.constant(8), ring.mul(ring.variable('gamma'), ring.mul(ring.power(a, 2), c)))
            degree = 18
        require(polynomial, 'unexpected leading cancellation at ' + name)
        for exponent in polynomial:
            require(sum(exponent[:len(witnesses)]) == degree, 'inhomogeneous leader at ' + name)
        leading[name] = degree, polynomial
        counts[operation] += 1
        producers[name] = (left, right)
        known.add(name)

    live = set()
    todo = [circuit['output']]
    while todo:
        name = todo.pop()
        if type(name) is not str or name in live:
            continue
        live.add(name)
        if name in producers:
            todo.extend(producers[name])
    require(live == known, 'dead gates or ports')
    require(len(gates) == 69 and counts == {'+': 15, '-': 14, '*': 40}, 'operation count mismatch')
    require(leading[circuit['output']][0] == 111, 'output degree mismatch')

    q = ring.mul(ring.variable('beta'), ring.variable('J'))
    k = ring.add(ring.variable('eta'), ring.variable('zeta'))
    c1 = ring.sub(ring.sub(q, ring.variable('F')), ring.variable('alpha'))
    transport = ring.sub(ring.mul(ring.variable('w'), c1), ring.mul(ring.variable('z'), q))
    expected = ring.constant(-8)
    for name, exponent in [('h', 1), ('gamma', 1), ('i', 2), ('w', 9), ('s', 18), ('T', 2), ('f', 4)]:
        expected = ring.mul(expected, ring.power(ring.variable(name), exponent))
    expected = ring.mul(expected, ring.mul(ring.power(q, 63), ring.mul(ring.power(k, 9), transport)))
    require(leading[circuit['output']][1] == expected, 'closed homogeneous formula mismatch')
    selected = dict(J=64, h=1, gamma=1, i=2, eta=9, w=9, s=18, T=2, f=4, z=1, beta=64)
    exponent = tuple(selected.get(name, 0) for name in names)
    require(expected.get(exponent) == 8, 'distinguished coefficient mismatch')

    provenance = circuit['provenance']
    source = ROOT / provenance['source']
    require(hashlib.sha256(source.read_bytes()).hexdigest() == provenance['sha256'], 'baseline source hash mismatch')
    baseline = json.loads(source.read_text())
    expected_gates = {row[0]: tuple(row[1:]) for row in baseline['source']}
    del expected_gates['scaled_f_square']
    expected_gates.update({
        'aux_coefficient_root': ('*', 'i', 'c2'),
        'strong_square_scaled': ('*', 'A', 'R16'),
        'norm_strong': ('-', 'L16', 'strong_square_scaled'),
        'aux_f2_minus_one': ('-', 'L16', 1),
        'aux_reduced_coefficient': ('*', 'A', 'aux_f2_minus_one'),
        'L17': ('*', 'aux_reduced_coefficient', 'aux_square_gap'),
        'polynomial': ('-', 'seven_units', 1),
    })
    require({row[0]: tuple(row[1:]) for row in gates} == expected_gates,
            'literal circuit differs from the specified baseline transformation')
    require(witnesses == baseline['witnesses'] and constants == baseline['fixed_numerals'],
            'changed source ports')
    binding = CIRCUIT.parent / circuit['coefficient_binding']['file']
    require(binding.is_file(), 'missing whole coefficient tuple binding')
    factors = ['norm_first', 'norm_main', 'norm_aux', 'norm_index', 'norm_transport', 'norm_strong']
    return dict(circuit_sha256=hashlib.sha256(CIRCUIT.read_bytes()).hexdigest(),
                baseline_sha256=provenance['sha256'], witnesses=15, fixed_ports=4,
                operations=69, multiplications=40, additions=15, subtractions=14,
                all_gates_live=True, all_ports_live=True,
                exact_degree=111, factor_degrees={name: leading[name][0] for name in factors},
                main_norm_identity=main_identity,
                leading_homogeneous_form='-8*Q^63*h*gamma*i^2*(eta+zeta)^9*w^9*s^18*T^2*f^4*(w*(Q-F-alpha)-z*Q), Q=beta*J',
                distinguished_monomial={name: exponent for name, exponent in selected.items() if name != 'beta'},
                distinguished_coefficient='8*beta^64',
                degree_hypothesis='beta != 0 (in particular beta = B-1 > 0)',
                formal_semantics='Local zero equivalence is certified in Lean; no native-window compiler correctness is asserted by this finite audit.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='replace the deterministic audit ledger')
    options = parser.parse_args()
    result = audit(json.loads(CIRCUIT.read_text()))
    encoded = json.dumps(result, indent=2) + '\n'
    if options.write:
        LEDGER.write_text(encoded)
    else:
        require(LEDGER.read_text() == encoded, 'ledger does not match (regenerate with --write)')
    print('PASS: 69 live gates, 15 positive witnesses, 4 fixed ports, exact degree 111')
