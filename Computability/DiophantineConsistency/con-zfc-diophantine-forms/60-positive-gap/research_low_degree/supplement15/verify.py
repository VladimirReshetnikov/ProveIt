#!/usr/bin/env python3
"""Independent exact audit of the degree-24 transport supplement.

No builder imports, interpolation, proof search, or consistency search.
All checks use exceptions and remain enabled under python -O.
"""
from collections import Counter, defaultdict
from pathlib import Path
import gzip
import hashlib
import json
import random

ROOT = Path(__file__).resolve().parent
VARIABLES = ['j', 'F', 'alpha', 'z', 'f', 'h', 'i', 'T', 'X', 'Y',
             'r', 'eta', 'zeta', 'u', 'gamma']
PORTS = ['beta', 'K0', 'MC', 'MF']


def need(ok, message):
    if not ok:
        raise ValueError(message)


def add(a, b, sign=1):
    result = defaultdict(int, a)
    for monomial, coefficient in b.items():
        result[monomial] += sign * coefficient
    return {m: c for m, c in result.items() if c}


def mul(a, b):
    result = defaultdict(int)
    for am, ac in a.items():
        for bm, bc in b.items():
            result[tuple(x+y for x, y in zip(am, bm))] += ac*bc
    return {m: c for m, c in result.items() if c}


def const(value, dimension):
    return {} if value == 0 else {(0,)*dimension: value}


def variable(index, dimension):
    return {tuple(int(i == index) for i in range(dimension)): 1}


def power(a, n):
    dimension = len(next(iter(a)))
    result = const(1, dimension)
    for _ in range(n):
        result = mul(result, a)
    return result


def packet(path):
    return json.loads((ROOT / path).read_text())


def topology(circuit):
    known = set(VARIABLES + PORTS)
    need(circuit['witnesses'] == VARIABLES, 'Wrong witness list')
    need(circuit['fixed_numerals'] == PORTS, 'Wrong port list')
    for name, op, x, y in circuit['source']:
        need(name not in known and op in ('+', '-', '*'), 'Bad producer')
        for value in (x, y):
            need(type(value) is int or isinstance(value, str) and value in known,
                 'Undefined operand')
        known.add(name)
    live = {circuit['output']}
    for name, op, x, y in reversed(circuit['source']):
        if name in live:
            live.update((x, y))
    need(all(row[0] in live for row in circuit['source']), 'Dead gate')
    need(set(VARIABLES + PORTS) <= live, 'Dead input')
    need(circuit['operations'] == len(circuit['source']), 'Wrong count')
    need(circuit['operation_breakdown'] == dict(Counter(row[1] for row in circuit['source'])),
         'Wrong operation breakdown')
    return len(circuit['source'])


def expression_keys(circuit):
    env = {name: ('leaf', name) for name in VARIABLES + PORTS}
    def value(x):
        return ('integer', x) if type(x) is int else env[x]
    for name, op, x, y in circuit['source']:
        pair = (value(x), value(y))
        if op in ('+', '*'):
            pair = tuple(sorted(pair, key=repr))
        env[name] = (op, *pair)
    return env


def evaluate(circuit, values, modulus=None):
    env = dict(values)
    def get(x): return x if type(x) is int else env[x]
    for name, op, x, y in circuit['source']:
        a, b = get(x), get(y)
        value = a+b if op == '+' else a-b if op == '-' else a*b
        env[name] = value if modulus is None else value % modulus
    return env


def exact_subexpression(circuit, output, overrides, dimension):
    definitions = {row[0]: row[1:] for row in circuit['source']}
    cache = dict(overrides)
    def visit(name):
        if type(name) is int:
            return const(name, dimension)
        if name in cache:
            return cache[name]
        need(name in definitions, 'Unexpected free input in local identity: ' + name)
        op, left, right = definitions[name]
        a, b = visit(left), visit(right)
        cache[name] = mul(a, b) if op == '*' else add(a, b, 1 if op == '+' else -1)
        return cache[name]
    return visit(output)


def transport_identity(baseline, revised):
    # Independent free ring Z[q,K,C,F,X,z].
    n = 6
    q, K, C, F, X, z = [variable(i, n) for i in range(n)]
    one = const(1, n)
    old_inner = add(add(mul(K, C), add(q, F, -1)),
                    mul(add(z, one), add(q, one, -1)), -1)
    old = add(add(mul(q, old_inner), mul(X, C)), q, -1)
    new = add(mul(C, add(mul(q, K), X)),
              mul(q, add(F, mul(z, add(q, one, -1)))), -1)
    need(old == new, 'Exact transport identity failed')
    overrides = {'q': q, 'qm': add(q, one, -1), 'qF': add(q, F, -1),
                 'K0': K, 'C': C, 'F': F, 'X': X, 'z': z}
    need(exact_subexpression(revised, revised['residuals'][3], overrides, n) == new,
         'Literal revised transport is not the displayed polynomial')
    overrides['z'] = add(z, one)
    need(exact_subexpression(baseline, baseline['residuals'][3], overrides, n) == old,
         'Literal baseline transport is not the displayed polynomial')
    return len(new)


def cancellation_identities(revised, certificate):
    # First-root cancellation, without assuming any equation.
    n = 5
    q, ell, r, Y, k = [variable(i, n) for i in range(n)]
    one = const(1, n)
    lhs = add(power(add(mul(power(q, 3), add(ell, r)), Y), 2),
              mul(power(q, 6), add(mul(ell, add(ell, k)), one)), -1)
    inner = add(add(power(r, 2), mul(ell, add(mul(const(2, n), r), k, -1))), one, -1)
    rhs = add(add(mul(power(q, 6), inner),
                  mul(mul(const(2, n), power(q, 3)), mul(add(ell, r), Y))), power(Y, 2))
    need(lhs == rhs, 'First-root cancellation failed')
    overrides = {'q': q, 'ell': ell, 'r': r, 'Y': Y, 'k': k}
    need(exact_subexpression(revised, revised['residuals'][0], overrides, n) == lhs,
         'Literal first-root evaluator mismatch')
    need(exact_subexpression(certificate, certificate['residuals'][0], overrides, n) == rhs,
         'Literal first-root certificate mismatch')
    # Main-root cancellation, with Delta=a^2+H and D0=ac+Z.
    n = 6
    q, a, c, X, Z, H = [variable(i, n) for i in range(n)]
    one, two = const(1, n), const(2, n)
    ac, D0, XH = mul(a, c), add(mul(a, c), Z), mul(X, H)
    lhs = add(power(add(mul(q, D0), XH), 2),
              mul(power(q, 2), add(mul(add(power(a, 2), H), power(c, 2)), one)), -1)
    norm = add(add(mul(mul(two, ac), Z), power(Z, 2)), mul(H, power(c, 2)), -1)
    rhs = add(add(mul(power(q, 2), add(norm, one, -1)),
                  mul(mul(two, q), mul(D0, XH))), power(XH, 2))
    need(lhs == rhs, 'Main-root cancellation failed')
    overrides = {'q': q, 'a': a, 'c': c, 'X': X, 'Z': Z, 'H': H}
    need(exact_subexpression(revised, revised['residuals'][1], overrides, n) == lhs,
         'Literal main-root evaluator mismatch')
    need(exact_subexpression(certificate, certificate['residuals'][1], overrides, n) == rhs,
         'Literal main-root certificate mismatch')


def degree_certificate(circuit):
    # Each pair stores an upper degree and its exact homogeneous component.
    # Fixed ports are formal degree-zero symbols, so no genericity assumption
    # or numerical substitution for the actual tuple enters the certificate.
    names = VARIABLES + PORTS
    n = len(names)
    env = {name: (int(i < len(VARIABLES)), variable(i, n))
           for i, name in enumerate(names)}
    def get(x): return (0, const(x, n)) if type(x) is int else env[x]
    for name, op, x, y in circuit['source']:
        dx, px = get(x)
        dy, py = get(y)
        if op == '*':
            env[name] = (dx+dy, mul(px, py))
        elif dx == dy:
            env[name] = (dx, add(px, py, 1 if op == '+' else -1))
        elif dx > dy:
            env[name] = (dx, px)
        else:
            env[name] = (dy, py if op == '+' else {m: -c for m, c in py.items()})
    degrees = [env[r][0] for r in circuit['residuals']]
    need(degrees == [11, 9, 4, 3, 12, 10], 'Residual degree upper bounds changed')
    v = {name: variable(names.index(name), n) for name in VARIABLES}
    k = add(v['eta'], v['zeta'])
    inner = add(mul(k, v['T']), mul(v['h'], v['X']))
    expected = const(4, n)
    for name, exponent in [('X', 4), ('Y', 6), ('f', 8), ('u', 2)]:
        expected = mul(expected, power(v[name], exponent))
    expected = mul(expected, power(inner, 2))
    degree, head = env[circuit['output']]
    need(degree == 24 and head == expected and bool(head), 'Exact top-degree form mismatch')
    witness = [0]*n
    for name, exponent in [('X', 6), ('Y', 6), ('f', 8), ('u', 2), ('h', 2)]:
        witness[names.index(name)] = exponent
    need(head.get(tuple(witness)) == 4, 'Degree-attaining coefficient is not four')
    return {'degree': 24, 'residual_degrees': degrees,
            'leading_form': '4*X^4*Y^6*f^8*u^2*((eta+zeta)*T+h*X)^2',
            'witness_monomial': 'X^6*Y^6*f^8*u^2*h^2', 'witness_coefficient': 4,
            'head_independent_of_all_fixed_ports': all(not any(m[len(VARIABLES):]) for m in head)}


def coefficients():
    source_binding = packet('native/COEFFICIENT_BINDING.json')
    need(source_binding['d'] == 590069, 'Wrong native tuple')
    values, files = {}, []
    for entry in source_binding['materialization']['files']:
        path = ROOT / 'native' / entry['file']
        compressed = path.read_bytes()
        raw = gzip.decompress(compressed)
        need(hashlib.sha256(raw).hexdigest() == entry['sha256'], 'Raw coefficient hash mismatch')
        need(len(raw) == entry['raw_bytes'], 'Coefficient size mismatch')
        value = int.from_bytes(raw, 'little')
        need(value.bit_length() == entry['bits'], 'Coefficient bit length mismatch')
        values[entry['port']] = value
        files.append({'port': entry['port'], 'bits': entry['bits'], 'raw_bytes': len(raw),
                      'sha256': entry['sha256']})
    need(set(values) == {'beta', 'K', 'MC', 'MF_source'}, 'Incomplete tuple')
    need(values['beta'] == (1 << 590069)-1, 'Wrong beta')
    native_high = values['MF_source'] - values['beta']
    need(0 < values['MC'] < values['beta'] and 0 < native_high < values['beta'], 'Bad masks')
    need(values['MC'] % 4 == 2 and native_high % 8 == 4, 'Mask congruence mismatch')
    need(values['MC'].bit_count()+native_high.bit_count() == 590069, 'Mask population mismatch')
    transitions = (ROOT / 'native' / 'k215_transitions.json').read_bytes()
    need(hashlib.sha256(transitions).hexdigest() == source_binding['transition_json_sha256'],
         'Wrong literal transition input')
    return {'beta': values['beta'], 'K0': values['K'], 'MC': values['MC'], 'MF': values['MF_source']}, files


def main():
    baseline = packet('circuits/p15_degree24_source58_baseline90.json')
    revised = packet('circuits/p15_degree24_transport89.json')
    certificate = packet('circuits/p15_degree24_transport89_degree_certificate.json')
    imported = packet('upstream/source58_p90.json')
    counts = [topology(x) for x in (baseline, revised, certificate, imported)]
    need(counts[:2] == [90, 89], 'The advertised improvement is not 90 to 89')
    original_expr, baseline_expr, revised_expr = map(expression_keys, (imported, baseline, revised))
    need(original_expr[imported['output']] == baseline_expr[baseline['output']],
         'Regenerated baseline differs from the pinned source58 evaluator')
    for index in (0, 1, 2, 4, 5):
        need(baseline_expr[baseline['residuals'][index]] == revised_expr[revised['residuals'][index]],
             'A non-transport residual changed')
    certificate_expr = expression_keys(certificate)
    for index in (2, 3, 4, 5):
        need(revised_expr[revised['residuals'][index]] == certificate_expr[certificate['residuals'][index]],
             'A non-rewritten residual differs in the degree certificate')
    transport_terms = transport_identity(baseline, revised)
    cancellation_identities(revised, certificate)
    degree = degree_certificate(certificate)
    ports, coefficient_files = coefficients()
    ones = {name: 1 for name in VARIABLES}
    small = evaluate(revised, ones | {name: 1 for name in PORTS})
    need(small['As'] == 81, 'The all-one obstruction changed')
    # The strong residual has no fixed-port ancestor.
    strong_text = repr(revised_expr['As'])
    need(all(repr(('leaf', name)) not in strong_text for name in PORTS),
         'All-one obstruction unexpectedly depends on a port')
    rng = random.Random(20261023)
    for _ in range(100):
        values = {name: rng.randrange(-5, 7) for name in VARIABLES}
        values.update({name: rng.randrange(-5, 7) for name in PORTS})
        ev_new = evaluate(revised, values)
        ev_old = evaluate(baseline, values | {'z': values['z']+1})
        ev_cert = evaluate(certificate, values)
        need(ev_new[revised['output']] == ev_old[baseline['output']] == ev_cert[certificate['output']],
             'Finite transcription check failed')
    # Actual fixed coefficients, reduced only for these finite implementation checks.
    for modulus in (1000003, 1000033):
        for _ in range(25):
            values = {name: rng.randrange(1, 20) for name in VARIABLES}
            values.update({name: value % modulus for name, value in ports.items()})
            new_value = evaluate(revised, values, modulus)[revised['output']]
            old_value = evaluate(baseline, values | {'z': values['z']+1}, modulus)[baseline['output']]
            need(new_value == old_value, 'Actual-tuple modular transcription check failed')
    receipt = {
        'status': 'PASS', 'baseline_operations': 90, 'revised_operations': 89,
        'revised_operation_breakdown': revised['operation_breakdown'],
        'positive_variables': 15, 'degree_certificate_evaluator_operations': counts[2],
        'exact_free_ring_transport_identity': True, 'transport_expanded_terms': transport_terms,
        'exact_free_ring_cancellation_identities': True,
        'baseline_expression_identical_to_pinned_source58': True,
        'non_transport_residuals_unchanged': True, 'degree_certificate': degree,
        'all_one_strong_residual': 81, 'all_one_polynomial_lower_bound': 6561,
        'signed_transcription_cases': 100, 'actual_tuple_modular_cases': 50,
        'coefficient_files': coefficient_files,
        'proof_boundary': 'Exact local algebra, degree, provenance and finite transcription checks; inherited unbounded compiler and object-ZFC derivation are not certified by this script.'
    }
    (ROOT / 'certificates' / 'VERIFY.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
