#!/usr/bin/env python3
"""Independent exact audit of the positive E=XY lift of the frozen P13 DAG.

Reads literal JSON, not either builder/checker. Standard library only.
Run from the final positive14 directory with no arguments, or supply paths.
This verifies finite algebra and binding, not the inherited unbounded theorem.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--packet-dir', type=Path, default=HERE)
parser.add_argument('--parent', type=Path)
parser.add_argument('--native-dir', type=Path)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
root = args.packet_dir.resolve()
parent_path = args.parent
if parent_path is None:
    local = root / 'p13_degree28.json'
    parent_path = local if local.exists() else root.parent / 'positive13' / 'p13_degree28.json'
native_dir = args.native_dir or root.parent / 'positive13' / 'native'
output_path = args.output or root / 'AUDIT14_INDEPENDENT.json'
packet_path = root / 'p14_degree24.json'
p = json.loads(packet_path.read_text())
parent = json.loads(parent_path.read_text())
parent_hash = '1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49'
require(sha(parent_path) == parent_hash, 'Parent is not the frozen P13 circuit')
require(p['source_circuit_sha256'] == parent_hash, 'Wrong source binding')
require(p['domain'] == parent['domain'] == 'strictly positive integers', 'Wrong domain')
require(p['witnesses'] == parent['witnesses'] + ['E'], 'Lift must add exactly E')
require(p['fixed_ports'] == parent['fixed_ports'] == ['beta', 'K0', 'MC', 'MF'], 'Native port change')
require(p['derived_fixed_leaves'] == parent['derived_fixed_leaves'], 'Fixed leaf rebinding')
require(p['coefficient_binding'] == parent['coefficient_binding'], 'Native tuple rebinding')
require(p['residuals'] == parent['residuals'] + ['AE'], 'Residual order change')

# Inspect the claimed definitional extension structurally. Only the defining
# gate's name changes; its old references become the new independent input E.
parent_end = max(j for j, row in enumerate(parent['source']) if row[0] in parent['residuals'])
expected_core = []
for name, op, x, y in parent['source'][:parent_end + 1]:
    if name == 'E':
        require((op, x, y) == ('*', 'X', 'Y'), 'Unexpected source definition of E')
        name = 'Eprod'
    expected_core.append([name, op, x, y])
expected_core.append(['AE', '-', 'E', 'Eprod'])
require(p['source'][:len(expected_core)] == expected_core, 'Lift changed another core gate')

# Coefficient payloads are shared with P13, with the shifted MF_source port.
expected_raw_hashes = {
    'beta': '0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d',
    'K': 'c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e',
    'MC': '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
    'MF_source': '48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737',
}
binding_path = native_dir / 'COEFFICIENT_BINDING.json'
binding = json.loads(binding_path.read_text())
require(binding['d'] == 590069 and binding['B'] == '2^590069', 'Wrong compact tuple')
payload_receipt = {}
entries = {row['port']: row for row in binding['materialization']['files']}
require(set(entries) == set(expected_raw_hashes), 'Native tuple is incomplete')
for name, digest in expected_raw_hashes.items():
    entry = entries[name]
    path = native_dir / entry['file']
    raw = gzip.decompress(path.read_bytes())
    require(hashlib.sha256(raw).hexdigest() == digest == entry['sha256'], 'Raw payload mismatch: ' + name)
    require(sha(path) == entry['gzip_sha256'], 'Compressed payload mismatch: ' + name)
    require(len(raw) == entry['raw_bytes'], 'Byte length mismatch: ' + name)
    value = int.from_bytes(raw, 'little')
    require(value > 0 and value.bit_length() == entry['bits'], 'Numeral size mismatch: ' + name)
    if name == 'beta':
        require(value == (1 << 590069) - 1, 'Beta numeral mismatch')
    payload_receipt[name] = {'raw_sha256': digest, 'raw_bytes': len(raw), 'bits': value.bit_length()}

# Independent sparse polynomial arithmetic. Packed exponents are justified by
# a separate uncancelled bound propagated through every fixed/circuit gate.
names = p['witnesses'] + p['fixed_ports']
witness_count = len(p['witnesses'])
BITS = 8
MASK = (1 << BITS) - 1
zero_bound = (0,) * len(names)
bounds = {name: tuple(int(j == k) for j in range(len(names))) for k, name in enumerate(names)}


def bound(expr):
    if isinstance(expr, int):
        return zero_bound
    if isinstance(expr, str):
        require(expr in bounds, 'Unbound circuit identifier: ' + expr)
        return bounds[expr]
    op, x, y = expr
    require(op in ('+', '-', '*'), 'Invalid arithmetic operation')
    a, b = bound(x), bound(y)
    return tuple(u + v if op == '*' else max(u, v) for u, v in zip(a, b))


for name, expr in p['derived_fixed_leaves'].items():
    require(name not in bounds, 'Duplicate fixed identifier')
    bounds[name] = bound(expr)
for name, op, x, y in p['source']:
    require(name not in bounds, 'Duplicate gate identifier')
    bounds[name] = bound([op, x, y])
require(max(max(row) for row in bounds.values()) < 1 << BITS, 'Exponent field overflow')


class Poly(dict):
    def __add__(self, other):
        if isinstance(other, int):
            other = {0: other} if other else {}
        out = Poly(self)
        for monomial, coefficient in other.items():
            c = out.get(monomial, 0) + coefficient
            if c:
                out[monomial] = c
            else:
                out.pop(monomial, None)
        return out

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.items()})

    def __sub__(self, other):
        return self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if isinstance(other, int):
            return Poly({m: c * other for m, c in self.items()}) if other else Poly()
        out = {}
        for m, c in self.items():
            for n, d in other.items():
                out[m + n] = out.get(m + n, 0) + c * d
        return Poly({m: c for m, c in out.items() if c})

    __rmul__ = __mul__

    def __pow__(self, power):
        require(isinstance(power, int) and power >= 0, 'Nonpolynomial exponent')
        result, factor = Poly({0: 1}), self
        while power:
            if power & 1:
                result = result * factor
            power //= 2
            if power:
                factor = factor * factor
        return result


one = Poly({0: 1})
generators = {name: Poly({1 << (BITS * j): 1}) for j, name in enumerate(names)}
env = dict(generators)


def evaluate(expr, table):
    if isinstance(expr, int):
        return expr * one
    if isinstance(expr, str):
        require(expr in table, 'Missing exact input: ' + expr)
        return table[expr]
    op, x, y = expr
    a, b = evaluate(x, table), evaluate(y, table)
    if op == '+':
        return a + b
    if op == '-':
        return a - b
    require(op == '*', 'Nonpolynomial operator')
    return a * b


for name, expr in p['derived_fixed_leaves'].items():
    env[name] = evaluate(expr, env)
for name, op, x, y in expected_core:
    env[name] = evaluate([op, x, y], env)

F, alpha, C, f0, i, T, X, Y, r, eta, zeta, u, gamma, E = [generators[name] for name in p['witnesses']]
beta, K0, MC, MF = [generators[name] for name in p['fixed_ports']]
q = F + alpha + C
k = eta + zeta
c = k * Y + eta
a = E + Y
H = 4 * a + 3
Delta = a * a + H
ell = E * k * Y
b = 3 * beta
b2 = b * b
L = beta * b2
Nf = b * f0 + q - beta - 1
I = i * c * c
Rhat = beta * ((q - 1) * (q - F) + alpha) * (q * q - 1) + (MC + q * MF) * (q - 1)
M0 = q**3 * (q - 1)
Bt = (q * K0 + X) * C - q * F
Ztail = M0 * r + (q - 1) * Y - q**3 * Bt
Mb = 4 * beta * q * q * Y
Sb = 4 * beta * q * Y
shift = Mb * gamma + Sb * X - beta * (k - 1) + Rhat
Vhat = Nf**2 * (beta * c * T - Rhat) - L * c

# Use cancelled identities, independently of the literal circuit's raw squares.
direct = [
    2 * M0 * ell * Ztail + Ztail**2 - M0**2 * (ell * k + 1),
    Mb**2 * (2 * a * c * X + X**2 - H * c**2 - 1)
    + 2 * Mb * (a * c + X) * H * shift + H**2 * shift**2,
    b2 * (Vhat + L * u)**2 - Delta * (Nf**2 - b2) * L * u * (2 * Vhat + L * u) - b2 * L**2,
    Nf**2 - b2 * (1 + Delta * I**2),
    E - X * Y,
]


def degree_of_monomial(m):
    return sum((m >> (BITS * j)) & MASK for j in range(witness_count))


def degree(poly):
    return max((degree_of_monomial(m) for m in poly), default=-1)


def monomial_text(m, selected_names, offset=0):
    factors = []
    for j, name in enumerate(selected_names, offset):
        exponent = (m >> (BITS * j)) & MASK
        if exponent:
            factors.append(name if exponent == 1 else name + '^' + str(exponent))
    return '*'.join(factors) or '1'


degree_receipt = []
witness_mask = (1 << (BITS * witness_count)) - 1
for name, formula, claimed_degree in zip(p['residuals'], direct, (12, 11, 12, 12, 2)):
    require(env[name] == formula, 'Independent identity failure: ' + name)
    require(degree(formula) == claimed_degree, 'Symbolic degree failure: ' + name)
    # A leading witness coefficient consisting of a single nonzero multiple of
    # beta^j cannot vanish under the authentic positive-beta specialization.
    coefficients = {}
    for monomial, coefficient in formula.items():
        if degree_of_monomial(monomial) == claimed_degree:
            witness_part = monomial & witness_mask
            coefficients.setdefault(witness_part, {})[monomial & ~witness_mask] = coefficient
    certificate = None
    for witness_part, fixed_coefficient in coefficients.items():
        if len(fixed_coefficient) == 1:
            fixed_part, scalar = next(iter(fixed_coefficient.items()))
            if fixed_part >> (BITS * (witness_count + 1)) == 0:
                certificate = {
                    'monomial': monomial_text(witness_part, p['witnesses']),
                    'coefficient': str(scalar) + '*' + monomial_text(fixed_part, p['fixed_ports'], witness_count),
                }
                break
    require(certificate is not None, 'No authentic-slice degree certificate: ' + name)
    degree_receipt.append({'residual': name, 'degree': claimed_degree, 'symbolic_terms': len(formula), 'authentic_degree_certificate': certificate})

strong = direct[3]
strong_leader = Poly({m: v for m, v in strong.items() if degree_of_monomial(m) == 12})
require(strong_leader == -9 * beta**2 * i**2 * (eta + zeta)**4 * Y**4 * (E + Y)**2, 'Strong leading form mismatch')
i_index = names.index('i')
for j in (0, 1, 2, 4):
    require(all(((m >> (BITS * i_index)) & MASK) == 0 for m in direct[j]), 'Another residual contains i')
selected = {'i': 4, 'eta': 8, 'E': 4, 'Y': 8}
selected_key = sum(power << (BITS * names.index(name)) for name, power in selected.items())
strong_square = strong**2
selected_coefficient = Poly({m & ~witness_mask: coefficient for m, coefficient in strong_square.items() if (m & witness_mask) == selected_key})
require(selected_coefficient == 81 * beta**4, 'Selected degree-24 coefficient failure')

# Check the finalizer over five free indeterminates. This avoids expanding the
# large full sum of squares and tests its exact arithmetic form independently.
cut = {name: generators[p['witnesses'][j]] for j, name in enumerate(p['residuals'])}
for name, op, x, y in p['source'][len(expected_core):]:
    cut[name] = evaluate([op, x, y], cut)
require(cut[p['output']] == sum((cut[name]**2 for name in p['residuals']), Poly()), 'Not exactly the five-square finalizer')

needed = {p['output']}
for name, op, x, y in reversed(p['source']):
    if name in needed:
        needed.update((x, y))
require(all(row[0] in needed for row in p['source']), 'Dead circuit gate')
require(set(names) <= needed, 'Dead witness or native port')
require(set(p['derived_fixed_leaves']) <= needed, 'Dead derived fixed leaf')
exact_support = {names[j] for polynomial in direct for monomial in polynomial for j in range(len(names)) if (monomial >> (BITS * j)) & MASK}
require(set(names) <= exact_support, 'An input cancels from every residual')
counts = dict(Counter(row[1] for row in p['source']))
require(counts == {'+': 26, '-': 17, '*': 58}, 'Operation count breakdown mismatch')
require(len(p['source']) == p['operations'] == 101, 'Operation total mismatch')
require(len(expected_core) == p['system_operations'] == 92, 'Core operation total mismatch')
require(p['residual_degrees'] == [12, 11, 12, 12, 2] and p['exact_degree'] == 24, 'Degree metadata mismatch')

receipt = {
    'status': 'PASS',
    'scope': 'Independent exact residual identities, pure definitional extension, authentic degree certificates, finalizer, liveness, gate census, and unchanged numerical coefficient tuple. Not an end-to-end formal consistency proof.',
    'parent_circuit_sha256': parent_hash,
    'circuit_sha256': sha(packet_path),
    'unknowns': 14,
    'domain': 'strictly positive integers',
    'operations': 101,
    'system_operations': 92,
    'operation_breakdown': counts,
    'fixed_leaf_convention': 'The same six derived fixed leaves as P13 are precomputed freely. Each binary arithmetic gate, including a square or scalar product, costs one.',
    'residuals': degree_receipt,
    'exact_total_degree': 24,
    'selected_monomial': 'i^4*eta^8*E^4*Y^8',
    'selected_coefficient': '81*beta^4',
    'all_witnesses_and_native_ports_live': True,
    'binding_sha256': sha(binding_path),
    'native_payloads': payload_receipt,
    'proof': 'Projection forgets E; its unique positive inverse is E=X*Y. The retained core is exactly P13 with its computed E promoted to an input, and AE=E-X*Y is a fifth squared residual.',
}
output_path.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
