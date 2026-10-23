#!/usr/bin/env python3
"""Independent stdlib P73 count/degree audit; uses no circuit-generator code."""
import argparse
import hashlib
import json
from pathlib import Path

# Only sparse integer polynomial primitives are shared with the independent P75 auditor.
from audit_sos_circuit import add, multiply, require

ROOT = Path(__file__).resolve().parents[3]
DIRECTORY = ROOT / 'Computability/DiophantineConsistency/circuits'
CIRCUIT = DIRECTORY / 'p73_sos.json'
LEDGER = DIRECTORY / 'p73_sos.audit.json'


def main_identity():
    zero = (0,) * 5
    variables = [{tuple(1 if k == j else 0 for k in range(5)): 1} for j in range(5)]
    a, c, x, g, h = variables
    ac = multiply(a, c)
    root = add(add(ac, x), g)
    source = add(multiply(root, root), multiply(add(multiply(a, a), h), multiply(c, c)), -1)
    term = add(add(multiply(x, x), multiply({zero: 2}, multiply(ac, add(x, g)))),
               add(multiply({zero: 2}, multiply(x, g)), multiply(g, g)))
    expanded = add(term, multiply(h, multiply(c, c)), -1)
    require(source == expanded, 'main norm polynomial identity')
    weights = (6, 5, 2, 7, 6)
    degrees = {m: sum(i * j for i, j in zip(m, weights)) for m in expanded}
    require(max(degrees.values()) == 18, 'main norm degree bound')
    require({m: k for m, k in expanded.items() if degrees[m] == 18} ==
            multiply({zero: 2}, multiply(ac, g)), 'main norm top form')
    return '(ac+X+g)^2-(a^2+H)c^2=X^2+2ac(X+g)+2Xg+g^2-Hc^2'


def audit(circuit):
    witnesses, ports, gates = (circuit[k] for k in ('witnesses', 'fixed_numerals', 'source'))
    require(len(witnesses) == 15 and len(ports) == 4, 'coordinate count')
    names = witnesses + ports
    require(len(set(names)) == 19, 'coordinate uniqueness')
    zero = (0,) * 19

    def constant(n):
        return {zero: n} if n else {}

    def variable(name):
        exponent = list(zero)
        exponent[names.index(name)] = 1
        return {tuple(exponent): 1}

    def power(value, n):
        result = constant(1)
        for _ in range(n):
            result = multiply(result, value)
        return result

    identity = main_identity()
    known = set(names)
    bounds = {name: (1 if name in witnesses else 0, variable(name)) for name in names}
    counts, producers = {'+': 0, '-': 0, '*': 0}, {}
    main_shapes = dict(cam2=('*', 'R10a', 'R12'), D1=('+', 'wn2', 'cam2'),
                       gam=('*', 'gamma', 'a4m5'), R14=('+', 'D1', 'gam'),
                       L15=('*', 'R14', 'R14'), a_square=('*', 'R12', 'R12'),
                       A=('+', 'a_square', 'a4m5'), c2=('*', 'R10a', 'R10a'),
                       Ac2=('*', 'A', 'c2'), a4=('*', 4, 'R12'), a4m5=('+', 'a4', 3))

    def operand(value):
        if type(value) is int:
            return 0, constant(value)
        require(type(value) is str and value in known, 'unavailable operand')
        return bounds[value]

    for row in gates:
        require(type(row) is list and len(row) == 4, 'gate shape')
        name, op, a, b = row
        require(type(name) is str and name not in known and op in counts, 'gate name/operation')
        if name in main_shapes:
            require((op, a, b) == main_shapes[name], 'main identity producer changed')
        da, pa = operand(a)
        db, pb = operand(b)
        if op == '*':
            degree, top = da + db, multiply(pa, pb)
        else:
            degree = max(da, db)
            top = add(pa if da == degree else {}, pb if db == degree else {}, 1 if op == '+' else -1)
        if name == 'norm_main':
            require((op, a, b) == ('-', 'L15', 'Ac2'), 'main norm cuts changed')
            require(bounds['R12'][0] == 6 and bounds['R10a'][0] == 5 and
                    bounds['wn2'][0] == 2 and bounds['gam'][0] == 7 and bounds['a4m5'][0] == 6,
                    'main norm cut weights')
            degree = 18
            top = multiply(constant(8), multiply(variable('gamma'),
                           multiply(power(bounds['R12'][1], 2), bounds['R10a'][1])))
        require(top and all(sum(m[:15]) == degree for m in top), 'top form or degree at ' + name)
        bounds[name] = degree, top
        counts[op] += 1
        producers[name] = a, b
        known.add(name)

    live, todo = set(), [circuit['output']]
    while todo:
        name = todo.pop()
        if type(name) is not str or name in live:
            continue
        live.add(name)
        if name in producers:
            todo.extend(producers[name])
    require(live == known, 'dead gates or ports')
    require(len(gates) == 73 and counts == {'+': 17, '-': 15, '*': 41}, 'gate counts')
    original_path = ROOT / circuit['provenance']['source']
    require(hashlib.sha256(original_path.read_bytes()).hexdigest() == circuit['provenance']['sha256'],
            'source hash')
    original = json.loads(original_path.read_text())
    require(witnesses == original['witnesses'] and ports == original['fixed_numerals'] and
            circuit['coefficient_binding'] == original['coefficient_binding'], 'ports/coefficient tuple changed')
    removed = {'norm_pair', 'norm_strong', 'norm_four', 'norm_product', 'all_units', 'seven_units', 'polynomial'}
    prefix = [row for row in original['source'] if row[0] not in removed]
    suffix = [
        ['first_main', '*', 'norm_first', 'norm_main'], ['aux_index', '*', 'norm_aux', 'norm_index'],
        ['aux_index_transport', '*', 'aux_index', 'norm_transport'],
        ['residual_first_main', '-', 'first_main', 1],
        ['residual_aux_index_transport', '-', 'aux_index_transport', 1],
        ['residual_strong', '-', 'aux_f2_minus_one', 'strong_square_scaled'],
        ['first_main_square', '*', 'residual_first_main', 'residual_first_main'],
        ['aux_index_transport_square', '*', 'residual_aux_index_transport', 'residual_aux_index_transport'],
        ['strong_residual_square', '*', 'residual_strong', 'residual_strong'],
        ['partial_sum', '+', 'first_main_square', 'aux_index_transport_square'],
        ['polynomial', '+', 'partial_sum', 'strong_residual_square'],
    ]
    require(len(prefix) == 62 and gates == prefix + suffix, 'literal grouping/producers changed')
    q, k = multiply(variable('beta'), variable('J')), add(variable('eta'), variable('zeta'))
    expected = multiply(constant(64), multiply(power(q, 50), power(k, 6)))
    for name, exponent in [('gamma', 2), ('w', 8), ('s', 14)]:
        expected = multiply(expected, power(variable(name), exponent))
    require(bounds['polynomial'] == (80, expected), 'degree/top formula')
    distinguished = dict(J=50, eta=6, gamma=2, w=8, s=14, beta=50)
    exponent = tuple(distinguished.get(name, 0) for name in names)
    require(expected.get(exponent) == 64, 'distinguished coefficient')
    require((CIRCUIT.parent / circuit['coefficient_binding']['file']).is_file(), 'coefficient binding absent')
    return dict(circuit_sha256=hashlib.sha256(CIRCUIT.read_bytes()).hexdigest(),
                source_sha256=circuit['provenance']['sha256'], operations=73, multiplications=41,
                additions=17, subtractions=15, all_gates_live=True, all_ports_live=True,
                witnesses=15, fixed_ports=4, retained_producers=62, finalizer_operations=11,
                exact_degree=80, main_norm_identity=identity,
                residual_degrees={name: bounds[name][0] for name in
                                  ['residual_first_main', 'residual_aux_index_transport', 'residual_strong']},
                leading_homogeneous_form='64*gamma^2*w^8*s^14*(eta+zeta)^6*(beta*J)^50',
                distinguished_monomial={name: n for name, n in distinguished.items() if name != 'beta'},
                distinguished_coefficient='64*beta^50', degree_hypothesis='beta != 0',
                proof_boundary='Lean checks literal equality, degree <=80 and local positive zero equivalence to P67; '
                               'the native-window compiler remains outside this certificate.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    options = parser.parse_args()
    encoded = json.dumps(audit(json.loads(CIRCUIT.read_text())), indent=2) + '\n'
    if options.write:
        LEDGER.write_text(encoded)
    else:
        require(LEDGER.read_text() == encoded, 'ledger differs; regenerate with --write')
    print('PASS: 73 live gates, 15 positive witnesses, 4 fixed ports, exact degree 80')
