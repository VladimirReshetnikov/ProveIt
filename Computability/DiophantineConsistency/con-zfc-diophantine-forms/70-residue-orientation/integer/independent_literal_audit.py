#!/usr/bin/env python3
"""Independent sparse-ring audit; does not import the construction builder.

This checks finite polynomial and coefficient claims, not the unbounded
Pell/compiler argument. Uses only the Python standard library.
"""
from pathlib import Path
import ast
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read(name):
    return json.loads((ROOT / name).read_text())


class Ring:
    """Sparse integer polynomials with sorted (variable, exponent) keys."""
    def __init__(self, terms):
        self.terms = {m: c for m, c in terms.items() if c}

    @classmethod
    def numeral(cls, value):
        return cls({(): value})

    @classmethod
    def variable(cls, name):
        return cls({((name, 1),): 1})

    def __add__(self, other):
        if isinstance(other, int):
            other = Ring.numeral(other)
        result = self.terms.copy()
        for m, c in other.terms.items():
            result[m] = result.get(m, 0) + c
        return Ring(result)

    __radd__ = __add__

    def __neg__(self):
        return Ring({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        if isinstance(other, int):
            other = Ring.numeral(other)
        return self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if isinstance(other, int):
            other = Ring.numeral(other)
        result = {}
        for m, c in self.terms.items():
            for n, d in other.terms.items():
                powers = dict(m)
                for x, p in n:
                    powers[x] = powers.get(x, 0) + p
                key = tuple(sorted(powers.items()))
                result[key] = result.get(key, 0) + c * d
        return Ring(result)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, 'invalid exponent')
        result = Ring.numeral(1)
        for _ in range(exponent):
            result = result * self
        return result

    def __eq__(self, other):
        if isinstance(other, int):
            other = Ring.numeral(other)
        return self.terms == other.terms

    def variables(self):
        return {name for monomial in self.terms for name, _ in monomial}

    def degree(self, variables):
        return max(sum(p for name, p in monomial if name in variables)
                   for monomial in self.terms)

    def coefficient(self, unknown_monomial, variables):
        result = {}
        wanted = tuple(sorted(unknown_monomial.items()))
        for monomial, value in self.terms.items():
            projected = tuple((name, p) for name, p in monomial if name in variables)
            if projected == wanted:
                fixed = tuple((name, p) for name, p in monomial if name not in variables)
                result[fixed] = value
        return Ring(result)


def expand(expression, symbols):
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return Ring.numeral(node.value)
        if isinstance(node, ast.Name):
            return symbols[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -visit(node.operand)
        if isinstance(node, ast.BinOp):
            left = visit(node.left)
            if isinstance(node.op, ast.Pow):
                require(isinstance(node.right, ast.Constant), 'nonliteral exponent')
                return left ** node.right.value
            right = visit(node.right)
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.Sub):
                return left - right
            if isinstance(node.op, ast.Mult):
                return left * right
        raise RuntimeError('nonpolynomial syntax')
    return visit(ast.parse(expression, mode='eval').body)


def main():
    parent_bytes = (ROOT / 'upstream/quartic41.json').read_bytes()
    parent = json.loads(parent_bytes)
    q40 = read('quartic40.json')
    direct = read('quartic40_direct.json')
    companions = [read('sextic34.json'), read('octic29.json')]
    packets = [direct, q40] + companions
    symbol_names = sorted(set(parent['variables'] + ['J3', 'w3', 'tau_tail', 'X3']
                              + parent['fixed_numerals']))
    sy = {name: Ring.variable(name) for name in symbol_names}
    old = [expand(row, sy) for row in parent['residuals']]
    new = [expand(row, sy) for row in q40['residuals']]
    require(hashlib.sha256(parent_bytes).hexdigest() == q40['parent_sha256'],
            'source packet hash mismatch')
    require(old[22] == sy['X'] - 2 * sy['u'] ** 2, 'wrong deleted row')
    sub = dict(sy, J=3 * sy['J3'] + 1, w_scale=3 * sy['w3'] + 1)
    expected = [expand(row, sub)
                for i, row in enumerate(parent['residuals']) if i != 22]
    require(expected == new, 'affine source restriction mismatch')
    require(set(q40['variables']) ==
            (set(parent['variables']) - {'J', 'w_scale', 'u'}) | {'J3', 'w3'},
            'quartic coordinate list mismatch')
    require(hashlib.sha256(parent_bytes).hexdigest() == direct['parent_sha256'],
            'direct source packet hash mismatch')
    require(direct['affine_source_coordinates'] == {'X': '3*X3-1'},
            'direct source substitution metadata mismatch')
    direct_sub = dict(sy, X=3 * sy['X3'] - 1)
    direct_expected = [expand(row, direct_sub)
                       for i, row in enumerate(parent['residuals']) if i != 22]
    require(direct_expected == [expand(row, sy) for row in direct['residuals']],
            'direct affine source restriction mismatch')
    require(direct['variables'] ==
            ['X3' if name == 'X' else name
             for name in parent['variables'] if name != 'u'],
            'direct quartic coordinate list mismatch')
    require(direct['coefficient_binding'] == q40['coefficient_binding'],
            'direct quartic changed fixed native tuple binding')
    require(direct['fixed_numerals'] == parent['fixed_numerals'],
            'direct fixed numeral ports mismatch')
    parent_polynomial = sum(r * r for r in old)
    require(parent_polynomial.degree(parent['variables']) == 4
            and len(parent_polynomial.terms) == 388,
            'source quartic degree or symbolic monomial count mismatch')
    restoration_counts = {}
    for packet in companions:
        restoration = {name: expand(expr, sy)
                       for name, expr in packet['restoration_to_quartic40'].items()}
        restored = [expand(row, dict(sy, **restoration)) for row in q40['residuals']]
        deleted = set(packet['deleted_quartic40_rows_zero_based'])
        require(all(restored[i] == 0 for i in deleted),
                packet['name'] + ': deleted row failed restoration')
        actual = [expand(row, sy) for row in packet['residuals']]
        require([r for i, r in enumerate(restored) if i not in deleted] == actual,
                packet['name'] + ': residual reconstruction mismatch')
        restoration_counts[packet['name']] = {
            'parent_rows_verified': len(restored),
            'deleted_rows_identically_zero': len(deleted),
            'surviving_rows_exactly_matched': len(actual)}

    metrics = []
    for packet in packets:
        variables = packet['variables']
        require(len(variables) == packet['variable_count'] == len(set(variables)),
                packet['name'] + ': variable count mismatch')
        residuals = [expand(row, sy) for row in packet['residuals']]
        require(len(residuals) == packet['equation_count'], 'row count mismatch')
        free = set().union(*(r.variables() for r in residuals))
        require(free == set(variables) | set(packet['fixed_numerals']),
                packet['name'] + ': undeclared or unused symbol')
        row_degrees = [r.degree(variables) for r in residuals]
        polynomial = sum(r * r for r in residuals)
        cert = packet['degree_certificate']
        coefficient = polynomial.coefficient(cert['monomial'], variables)
        require(coefficient == cert['coefficient'], 'exact coefficient mismatch')
        require(polynomial.degree(variables) == packet['exact_degree'],
                packet['name'] + ': exact degree mismatch')
        if packet is direct:
            require(len(polynomial.terms) == 393 and max(row_degrees) == 2,
                    'direct quartic symbolic size or row degree mismatch')
        metrics.append({'name': packet['name'], 'variables': len(variables),
                        'residuals': len(residuals), 'row_degrees': row_degrees,
                        'exact_degree': packet['exact_degree'],
                        'symbolic_monomials': len(polynomial.terms),
                        'certificate_coefficient': cert['coefficient']})

    binding = read('upstream/PAYLOAD_BINDING.json')
    coefficient_checks = {}
    coefficients = {}
    for name, metadata in binding['payloads'].items():
        compressed = (ROOT / 'coefficients' / (name + '.bin.gz')).read_bytes()
        raw = gzip.decompress(compressed)
        value = int.from_bytes(raw, 'little')
        require(hashlib.sha256(raw).hexdigest() == metadata['sha256'],
                name + ': fixed numeral hash mismatch')
        require(value.bit_length() == metadata['bits'] and len(raw) == metadata['bytes'],
                name + ': fixed numeral size mismatch')
        coefficients[name] = value
        coefficient_checks[name] = {'sha256': metadata['sha256'],
                                    'bit_length': value.bit_length(), 'bytes': len(raw)}
    beta = coefficients['beta']
    require(beta == 2**1064921 - 1 and beta % 3 == 1, 'radix orientation mismatch')
    require(0 < coefficients['MC'] < beta < coefficients['MF_source'] < 2 * beta,
            'native mask magnitude hypotheses failed')
    require(coefficients['K'] >= 0, 'native transport coefficient negative')
    # Independent algebraic identity used in the uniform signed growth proof.
    U, Z = Ring.variable('U'), Ring.variable('Z')
    difference = ((2 * ((U - 1) * Z - 2) - 1)**2
                  - 2 * (2 * U * Z**2 + 1) * (U - 3))
    require(difference == 4 * (U + 1) * Z**2 - 20 * (U - 1) * Z + 31 - 2 * U,
            'signed ratio difference identity mismatch')
    result = {'status': 'PASS', 'checker': 'independent standard-library sparse ring; builder not imported',
              'scope': 'literal substitutions, restorations, degrees, coefficients, fixed payloads',
              'source_pin': q40['source_pin'], 'packets': metrics,
              'source_parent': {'variables': len(parent['variables']),
                                'residuals': len(old), 'exact_degree': 4,
                                'symbolic_monomials': len(parent_polynomial.terms)},
              'direct_source_substitution': 'X_old=3*X3-1; delete u and row 22',
              'restorations': restoration_counts, 'coefficients': coefficient_checks,
              'signed_ratio_identity': '4(U+1)Z^2-20(U-1)Z+31-2U'}
    target = ROOT / 'certificates/INDEPENDENT_LITERAL_AUDIT.json'
    target.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
