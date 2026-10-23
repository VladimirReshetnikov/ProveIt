#!/usr/bin/env python3
"""Independent stdlib audit of P77 liveness, counts, provenance and exact degree.

The symbolic recurrence retains a valid degree envelope even when its top
homogeneous component cancels. Thus no special assumption about the main Pell
norm is needed. A nonzero final homogeneous component proves exact degree.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
DIRECTORY = ROOT / 'Computability/DiophantineConsistency/circuits'
CIRCUIT = DIRECTORY / 'p77_sos.json'
LEDGER = DIRECTORY / 'p77_sos.audit.json'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(left, right, sign=1):
    result = dict(left)
    for exponent, coefficient in right.items():
        result[exponent] = result.get(exponent, 0) + sign * coefficient
        if not result[exponent]:
            del result[exponent]
    return result


def multiply(left, right):
    result = {}
    for a, c in left.items():
        for b, d in right.items():
            exponent = tuple(x + y for x, y in zip(a, b))
            result[exponent] = result.get(exponent, 0) + c * d
    return {a: c for a, c in result.items() if c}


def audit(circuit, circuit_path):
    witnesses, ports, gates = (circuit[k] for k in ('witnesses', 'fixed_numerals', 'source'))
    require(len(witnesses) == 15 and len(set(witnesses)) == 15, 'witness count')
    require(len(ports) == 4 and len(set(ports)) == 4, 'fixed port count')
    names = witnesses + ports
    require(len(set(names)) == len(names), 'overlapping coordinate names')
    zero = (0,) * len(names)

    def constant(n):
        return {zero: n} if n else {}

    def variable(name):
        exponent = list(zero)
        exponent[names.index(name)] = 1
        return {tuple(exponent): 1}

    def power(value, exponent):
        result = constant(1)
        for _ in range(exponent):
            result = multiply(result, value)
        return result

    known = set(names)
    bounds = {n: (1 if n in witnesses else 0, variable(n)) for n in names}
    producers, counts = {}, {'+': 0, '-': 0, '*': 0}

    def operand(value):
        if type(value) is int:
            return 0, constant(value)
        require(type(value) is str and value in known, 'unavailable input ' + str(value))
        return bounds[value]

    for row in gates:
        require(type(row) is list and len(row) == 4, 'invalid row')
        name, operation, a, b = row
        require(type(name) is str and name not in known, 'duplicate gate')
        require(operation in counts, 'invalid operation')
        da, pa = operand(a)
        db, pb = operand(b)
        if operation == '*':
            degree, top = da + db, multiply(pa, pb)
        else:
            degree = max(da, db)
            top = add(pa if da == degree else {}, pb if db == degree else {},
                      1 if operation == '+' else -1)
        require(all(sum(exponent[:len(witnesses)]) == degree for exponent in top),
                'incorrect homogeneous weight at ' + name)
        bounds[name] = degree, top
        producers[name] = a, b
        known.add(name)
        counts[operation] += 1

    live, todo = set(), [circuit['output']]
    while todo:
        name = todo.pop()
        if type(name) is not str or name in live:
            continue
        live.add(name)
        if name in producers:
            todo.extend(producers[name])
    require(live == known, 'dead gates or ports: ' + str(sorted(known - live)))
    count = len(gates)
    require(count in (75, 77), 'operation count')
    compact = count == 75
    require(counts == ({'+': 18, '-': 16, '*': 41} if compact else {'+': 19, '-': 17, '*': 41}),
            'operation distribution')

    source_path = ROOT / circuit['provenance']['source']
    require(hashlib.sha256(source_path.read_bytes()).hexdigest() ==
            circuit['provenance']['sha256'], 'source hash mismatch')
    source = json.loads(source_path.read_text())
    require(witnesses == source['witnesses'] and ports == source['fixed_numerals'], 'coordinate order')
    require(circuit['coefficient_binding'] == source['coefficient_binding'], 'coefficient tuple changed')
    removed = {'norm_pair', 'norm_strong', 'norm_four', 'norm_product',
               'all_units', 'seven_units', 'polynomial'}
    prefix = [row for row in source['source'] if row[0] not in removed]
    require(gates[:len(prefix)] == prefix, 'changed retained producers')
    if compact:
        residuals = [('residual_first', 'norm_first', 1), ('residual_aux', 'norm_aux', 1),
                     ('residual_strong', 'aux_f2_minus_one', 'strong_square_scaled'),
                     ('residual_main_index_transport', 'main_index_transport', 1)]
        suffix = [['main_index', '*', 'norm_main', 'norm_index'],
                  ['main_index_transport', '*', 'main_index', 'norm_transport']]
    else:
        residuals = [('residual_first', 'norm_first', 1), ('residual_main', 'norm_main', 1),
                     ('residual_aux', 'norm_aux', 1),
                     ('residual_strong', 'aux_f2_minus_one', 'strong_square_scaled'),
                     ('residual_index_transport', 'index_transport', 1)]
        suffix = [['index_transport', '*', 'norm_index', 'norm_transport']]
    suffix.extend([[name, '-', left, right] for name, left, right in residuals])
    suffix.extend([[name + '_square', '*', name, name] for name, _, _ in residuals])
    if compact:
        suffix.extend([
            ['sum_1', '+', 'residual_first_square', 'residual_aux_square'],
            ['sum_2', '+', 'sum_1', 'residual_strong_square'],
            ['polynomial', '+', 'sum_2', 'residual_main_index_transport_square'],
        ])
    else:
        suffix.extend([
            ['sum_1', '+', 'residual_first_square', 'residual_main_square'],
            ['sum_2', '+', 'sum_1', 'residual_aux_square'],
            ['sum_3', '+', 'sum_2', 'residual_strong_square'],
            ['polynomial', '+', 'sum_3', 'residual_index_transport_square'],
        ])
    require(gates[len(prefix):] == suffix, 'changed residual matrix/finalizer')
    require(len(prefix) == 62, 'retained-prefix count')
    require(bounds[circuit['output']][0] == 68, 'degree upper bound')
    q = multiply(variable('beta'), variable('J'))
    k = add(variable('eta'), variable('zeta'))
    expected = multiply(power(q, 40), power(k, 8))
    for name, exponent in [('i', 4), ('w', 4), ('s', 12)]:
        expected = multiply(expected, power(variable(name), exponent))
    require(bounds[circuit['output']][1] == expected, 'leading homogeneous form')
    distinguished = dict(J=40, eta=8, i=4, w=4, s=12, beta=40)
    exponent = tuple(distinguished.get(name, 0) for name in names)
    require(expected.get(exponent) == 1, 'distinguished coefficient')
    binding = circuit_path.parent / circuit['coefficient_binding']['file']
    require(binding.is_file(), 'missing complete coefficient binding')
    return dict(
        circuit_sha256=hashlib.sha256(circuit_path.read_bytes()).hexdigest(),
        source_sha256=circuit['provenance']['sha256'], operations=count,
        multiplications=counts['*'], additions=counts['+'], subtractions=counts['-'],
        retained_producers=62, finalizer_operations=count - 62,
        all_gates_live=True, all_ports_live=True, witnesses=15, fixed_ports=4,
        degree_upper_bound=68, exact_degree=68,
        residual_degree_upper_bounds={name: bounds[name][0] for name, _, _ in residuals},
        leading_homogeneous_form='i^4*w^4*s^12*(eta+zeta)^8*(beta*J)^40',
        distinguished_monomial={n: e for n, e in distinguished.items() if n != 'beta'},
        distinguished_coefficient='beta^40', degree_hypothesis='beta != 0',
        proof_boundary='Lean checks literal evaluator equality and local positive zero equivalence '
                       'to P67. This finite audit does not certify the native-window compiler.',
    )


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    arguments = parser.parse_args()
    for count in (75, 77):
        circuit = DIRECTORY / f'p{count}_sos.json'
        ledger = DIRECTORY / f'p{count}_sos.audit.json'
        result = audit(json.loads(circuit.read_text()), circuit)
        encoded = json.dumps(result, indent=2) + '\n'
        if arguments.write:
            ledger.write_text(encoded)
        else:
            require(ledger.read_text() == encoded, 'ledger differs; regenerate with --write')
        print(f'PASS: {count} live gates, 15 positive witnesses, 4 fixed ports, exact degree 68')
