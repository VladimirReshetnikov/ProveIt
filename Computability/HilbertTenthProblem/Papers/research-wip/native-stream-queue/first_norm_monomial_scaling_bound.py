#!/usr/bin/env python3
"""Fresh bounded audit; frozen predecessors are read only as bytes/JSON."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

PINS = {
    'first_norm_five_gate_lower_bound.py': '2eecbcfa6d48872f8522cdb839517232a2208cfc9f9466f5780c3d0584ddb077',
    'first_norm_five_gate_lower_bound.json': 'e66759e01ae27cb41abe419a3875180c68467363c3c249943bbc8c589552fee4',
    'first_norm_five_gate_lower_bound.md': '3f7580635b63b6cc7bda27b23022db99c85fdc4341c34ea1fb5d55f42e00c2fc',
    'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
    'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
}

def check(condition, message):
    if not condition:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()

def read_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            check(key not in result, 'duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=pairs)

def exact(left, right):
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return left.keys() == right.keys() and all(exact(left[k], right[k]) for k in left)
    if isinstance(left, list):
        return len(left) == len(right) and all(exact(a, b) for a, b in zip(left, right))
    return left == right

# Sparse polynomials use exponent tuples in T,X,Y,k.
ZERO = (0, 0, 0, 0)
def add(a, b, scale=1):
    result = dict(a)
    for power, coefficient in b.items():
        result[power] = result.get(power, 0) + scale * coefficient
        if result[power] == 0:
            del result[power]
    return result

def mul(a, b):
    result = {}
    for u, x in a.items():
        for v, y in b.items():
            p = tuple(i + j for i, j in zip(u, v))
            result[p] = result.get(p, 0) + x*y
    return {p: c for p, c in result.items() if c}

def serialize(p):
    return [{'powers': list(k), 'coefficient': v} for k, v in sorted(p.items())]

def specialize_y_one(p):
    result = {}
    for (t, x, y, k), c in p.items():
        v = (t, x, k)
        result[v] = result.get(v, 0) + c
    return {v: c for v, c in result.items() if c}

def build(root):
    for name, sha in PINS.items():
        check(digest((root/name).read_bytes()) == sha, 'pin mismatch: ' + name)
    previous = read_json(root/'first_norm_five_gate_lower_bound.json')
    parent = read_json(root/'complete84_scaled_strong_output.json')['packet']
    rows = parent['source']
    check(len(rows) == 84, '84 source length')
    known = set(parent['free'])
    definitions = {}
    for row in rows:
        name, op, a, b = row
        check(name not in known and op in ('+', '-', '*'), 'source row')
        check(all(type(v) is int or v in known for v in (a, b)), 'source closure')
        definitions[name] = row
        known.add(name)
    live = {parent['output']}
    for name, op, a, b in reversed(rows):
        if name in live:
            live.update(v for v in (a, b) if type(v) is str)
    check(live == set(parent['free']) | set(definitions), 'full source liveness')
    block_names = ['tau_square', 'first_root_base', 'first_next', 'first_product', 'norm_first']
    block = [definitions[name] for name in block_names]
    check(block == previous['attainment'][0]['block'], 'current literal first norm')
    check(definitions['UM'] == ['UM', '*', 'wn2', 'sn2'], 'E=XY')
    check(definitions['ksn2'] == ['ksn2', '*', 'R10b', 'sn2'], 'Z=kY')
    check(definitions['R10b'] == ['R10b', '+', 'eta', 'zeta'], 'k positive chart')
    check(sum(row[1] == '*' for row in block) == 3, 'three products')
    check(sum(row[1] in ('+', '-') for row in block) == 2, 'two additions')
    unit = [{tuple(int(i == j) for i in range(4)): 1} for j in range(4)]
    T, X, Y, k = unit
    E, Z = mul(X, Y), mul(k, Y)
    env = dict(zip(['tau_root', 'wn2', 'sn2', 'R10b', 'UM', 'ksn2'], [T, X, Y, k, E, Z]))
    for name, op, a, b in block:
        env[name] = mul(env[a], env[b]) if op == '*' else add(env[a], env[b], -1 if op == '-' else 1)
    target = {(2, 0, 0, 0): 1, (0, 2, 4, 2): -1, (0, 1, 2, 2): -1}
    check(env['norm_first'] == target, 'exact dependent-port polynomial')
    restricted = specialize_y_one(target)
    check(restricted == {(2, 0, 0): 1, (0, 2, 2): -1, (0, 1, 2): -1}, 'quartic restriction')
    check(previous['forced_cubic_coefficient'] == [], 'authenticated quartic contradiction')
    check(previous['required_cubic_coefficient'] == -1, 'required cubic contradiction')
    radicand = mul(mul(k, Y), mul(k, Y))
    radicand = mul(mul(radicand, X), add(mul(X, mul(Y, Y)), {ZERO: 1}))
    check(min(p[1] for p in radicand) == 1, 'odd X valuation of radicand')
    check(add(mul(T, T), radicand, -1) == target, 'quadratic radicand')
    cases = []
    # Finite corroboration only. The companion proves all nonnegative powers.
    for powers in itertools.product(range(3), repeat=6):
        a, b, c, d, e, f = powers
        normalized = (a, b+e, c+e+f, d+f)
        multiplier = {ZERO: 1}
        for poly, exponent in zip([T, X, Y, k, E, Z], powers):
            for unused in range(exponent):
                multiplier = mul(multiplier, poly)
        check(multiplier == {normalized: 1}, 'six-port monomial normalization')
        scaled = mul(multiplier, target)
        small = specialize_y_one(scaled)
        degree = max(sum(p) for p in small)
        check(len(scaled) == len(small) == 3, 'three distinct shifted monomials')
        check(degree == 4+a+b+e+d+f, 'restricted degree formula')
        branch = 'quartic contradiction' if a+b+e+d+f == 0 else 'degree greater than four'
        check(degree == 4 if branch == 'quartic contradiction' else degree > 4, 'proof branch')
        cases.append({'powers': list(powers), 'normalized': list(normalized), 'restricted_degree': degree, 'branch': branch})
    return {
        'status': 'PASS_FIRST_NORM_MONOMIAL_SCALING_COMPONENT_BOUND',
        'source_sha256': digest(Path(__file__).read_bytes()),
        'pins': PINS,
        'scope': 'Exact division-free component at T,X,Y,k,E=XY,Z=kY only; arbitrary nonzero rational scalar and nonnegative integer monomial powers. No global bound, added free multiplier port, changed coordinates or general positive polynomial multipliers.',
        'parent_source': {'rows': 84, 'canonical_source_sha256': digest(canonical(rows)), 'all_rows_and_ports_live': True, 'first_norm': block, 'dependent_producers': [definitions['UM'], definitions['ksn2']]},
        'target': serialize(target),
        'radicand': serialize(radicand),
        'radicand_X_valuation': 1,
        'theorem': {'multiplications_at_least': 3, 'additions_subtractions_at_least': 2, 'total_at_least': 5, 'each_bound_allows_unbounded_other_operations': True},
        'normalization': 'T^a X^b Y^c k^d E^e Z^f = T^a X^(b+e) Y^(c+e+f) k^(d+f)',
        'restricted_degree': '4+a+b+e+d+f',
        'finite_corroboration': {'cases': len(cases), 'quartic_branch': sum(x['branch'] == 'quartic contradiction' for x in cases), 'degree_branch': sum(x['branch'] != 'quartic contradiction' for x in cases), 'cases_sha256': digest(canonical(cases))},
    }

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = build(args.root)
    if args.expect:
        check(exact(result, read_json(args.expect)), 'recursive type-exact receipt mismatch')
    if args.output:
        args.output.write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(result['status'])

if __name__ == '__main__':
    main()
