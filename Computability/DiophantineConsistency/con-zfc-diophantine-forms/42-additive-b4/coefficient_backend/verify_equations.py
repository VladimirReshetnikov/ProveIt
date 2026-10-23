#!/usr/bin/env python3
"""Check concrete equations, coherent coefficient bindings and exact degrees.

A nonzero leading coefficient after x_i=a_i*t modulo a fixed modulus is an
exact lower-degree certificate; it is not random identity testing. The DAG,
with the main norm's exact distributive cancellation, gives the matching
upper bound. No polynomial solution is sought.
"""
from pathlib import Path
from hashlib import sha256
import gzip
import json
import random

HERE = Path(__file__).resolve().parent
MODULUS = 1000000007


def need(condition, message):
    if not condition:
        raise ValueError(message)


def trim(poly):
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def add(a, b, sign=1):
    return trim([((a[i] if i < len(a) else 0) + sign *
                  (b[i] if i < len(b) else 0)) % MODULUS
                 for i in range(max(len(a), len(b)))])


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % MODULUS
    return trim(out)


def norm_upper_bound(graph, target, atoms, degrees):
    """Exact sparse expansion in five cut variables: a,c,X,H,gamma."""
    zero = (0,) * len(atoms)
    memo = {}
    for i, atom in enumerate(atoms):
        power = list(zero)
        power[i] = 1
        memo[atom] = {tuple(power): 1}

    def expand(key):
        if isinstance(key, int):
            return {zero: key} if key else {}
        if key in memo:
            return memo[key]
        operation, left, right = graph[key]
        a, b = expand(left), expand(right)
        out = {}
        if operation == '*':
            for ea, ca in a.items():
                for eb, cb in b.items():
                    e = tuple(x + y for x, y in zip(ea, eb))
                    out[e] = out.get(e, 0) + ca * cb
        else:
            out = a.copy()
            sign = 1 if operation == '+' else -1
            for e, c in b.items():
                out[e] = out.get(e, 0) + sign * c
        memo[key] = {e: c for e, c in out.items() if c}
        return memo[key]

    expansion = expand(target)
    weighted_degree = max(sum(e * degrees[a] for e, a in zip(exponents, atoms))
                          for exponents in expansion)
    need(weighted_degree == 18, 'main norm cancellation')
    return weighted_degree, {'target': target, 'atoms': atoms,
                             'atom_degree_bounds': [degrees[a] for a in atoms],
                             'terms': [{'powers': list(e), 'coefficient': c}
                                       for e, c in sorted(expansion.items())],
                             'weighted_degree_bound': weighted_degree}


def check(name):
    circuit = json.loads((HERE / 'equations' / name).read_text())
    provenance = circuit['provenance']
    source_file = HERE / 'equations' / provenance['upstream_file']
    upstream = json.loads(source_file.read_text())
    need(sha256(source_file.read_bytes()).hexdigest() == provenance['sha256'],
         'upstream digest')
    for key in ('source', 'witness_domain', 'witnesses', 'fixed_numerals',
                'output', 'comparisons'):
        need(circuit.get(key) == upstream.get(key), 'changed graph/interface: ' + key)

    binding_path = HERE / 'equations' / circuit['coefficient_binding']['file']
    binding = json.loads(binding_path.read_text())
    need(binding['d'] == 683195, 'wrong coefficient backend')
    actual = {}
    hashes = {}
    for record in binding['materialization']['files']:
        raw = gzip.decompress((binding_path.parent / record['file']).read_bytes())
        need(sha256(raw).hexdigest() == record['sha256'], 'coefficient digest')
        actual[record['port']] = int.from_bytes(raw, 'little')
        hashes[record['port']] = record['sha256']
    need(hashes == circuit['coefficient_binding']['port_sha256'], 'binding hash table')
    constants = {name: actual[port] for name, port in
                 circuit['coefficient_binding']['aliases'].items()}
    need(set(constants) == set(circuit['fixed_numerals']), 'free coefficient port')

    rng = random.Random(683195)
    slopes = {x: rng.randrange(1, MODULUS) for x in circuit['witnesses']}
    polynomials = {x: [0, a] for x, a in slopes.items()}
    polynomials.update({x: [a % MODULUS] for x, a in constants.items()})
    degrees = {x: 1 for x in slopes}
    degrees.update({x: 0 for x in constants})
    dependencies = {x: {x} for x in polynomials}
    nodes = set()
    multiplication_count = 0
    graph = {row[0]: row[1:] for row in circuit['source']}
    cancellation_certificate = None

    def poly(x):
        return [x % MODULUS] if isinstance(x, int) else polynomials[x]

    def degree(x):
        return 0 if isinstance(x, int) else degrees[x]

    def deps(x):
        return set() if isinstance(x, int) else dependencies[x]

    for target, op, left, right in circuit['source']:
        need(target not in polynomials, 'duplicate output')
        need(op in ('+', '-', '*'), 'unsupported gate')
        a, b = poly(left), poly(right)
        polynomials[target] = (mul(a, b) if op == '*' else
                               add(a, b, 1 if op == '+' else -1))
        degrees[target] = (degree(left) + degree(right) if op == '*'
                           else max(degree(left), degree(right)))
        if target in ('norm_main', 'N1'):
            atoms = (['R12', 'R10a', 'wn2', 'a4m5', 'gamma']
                     if target == 'norm_main' else ['a', 'c', 'X', 'H', 'gamma'])
            degrees[target], cancellation_certificate = norm_upper_bound(
                graph, target, atoms, degrees)
        dependencies[target] = deps(left) | deps(right) | {target}
        nodes.add(target)
        multiplication_count += op == '*'

    if 'output' in circuit:
        outputs = [(circuit['output'], 0)]
        claimed = [circuit['exact_degree']]
    else:
        outputs = circuit['comparisons']
        claimed = circuit['residual_exact_degrees']
    degree_certificates = []
    live = set()
    for (left, right), expected in zip(outputs, claimed):
        value = add(poly(left), poly(right), -1)
        upper = max(degree(left), degree(right))
        need(upper == expected, 'degree upper bound changed')
        need(len(value) - 1 == expected and value[-1] != 0,
             'lower-degree certificate failed')
        degree_certificates.append({'comparison': [left, right], 'upper_bound': upper,
                                     'degree_on_fixed_line': len(value) - 1,
                                     'leading_coefficient_mod_m': value[-1]})
        live |= deps(left) | deps(right)
    need(nodes <= live, 'unused gate')
    need(set(constants) <= live, 'unused coefficient')
    need(set(slopes) <= live, 'unused witness')
    need(len(nodes) == circuit['ledger']['operations'], 'operation count')
    need(multiplication_count == circuit['ledger']['multiplications'], 'multiplication count')

    return {'file': name, 'status': 'PASS', 'graph_identical_to_upstream': True,
            'domain': circuit['witness_domain'], 'unknowns': len(slopes),
            'equations': len(outputs), 'degree': max(claimed),
            'operations': len(nodes), 'multiplications': multiplication_count,
            'additions_subtractions': len(nodes) - multiplication_count,
            'all_gates_live': True, 'all_ports_fixed_and_live': True,
            'port_sha256': hashes, 'modulus': MODULUS, 'fixed_line_slopes': slopes,
            'main_norm_cancellation_certificate': cancellation_certificate,
            'exact_degree_certificates': degree_certificates}


if __name__ == '__main__':
    checks = [check('product67_nonzero683195.json'),
              check('retained16_system59_nonzero683195.json')]
    result = {'status': 'PASS', 'scope': 'Exact graph/binding/degree certificate; universal semantics are in PROOF.md and the inherited proofs.',
              'circuits': checks}
    (HERE / 'equations' / 'VERIFICATION.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
