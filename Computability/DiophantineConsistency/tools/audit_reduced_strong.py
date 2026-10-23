#!/usr/bin/env python3
"""Independent stdlib gate, exact-cancellation, and degree audit for P76."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
CIRCUIT = ROOT / 'Computability/DiophantineConsistency/circuits/p76_sos.json'
LEDGER = CIRCUIT.with_name('p76_sos.audit.json')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(left, right, sign=1):
    result = dict(left)
    for exponent, coefficient in right.items():
        result[exponent] = result.get(exponent, 0) + sign * coefficient
        if result[exponent] == 0:
            del result[exponent]
    return result


def multiply(left, right):
    result = {}
    for a, c in left.items():
        for b, d in right.items():
            exponent = tuple(x + y for x, y in zip(a, b))
            result[exponent] = result.get(exponent, 0) + c * d
    return {a: c for a, c in result.items() if c}


def audit():
    circuit = json.loads(CIRCUIT.read_text())
    source_path = ROOT / circuit['provenance']['source']
    require(hashlib.sha256(source_path.read_bytes()).hexdigest() ==
            circuit['provenance']['sha256'], 'source hash')
    source = json.loads(source_path.read_text())
    witnesses, ports = circuit['witnesses'], circuit['fixed_numerals']
    require(witnesses == source['witnesses'] and len(witnesses) == 15, 'witness coordinates')
    require(ports == source['fixed_numerals'] and len(ports) == 4, 'coefficient ports')
    require(circuit['coefficient_binding'] == source['coefficient_binding'], 'coefficient binding')
    gates = circuit['source']
    old = {row[0]: row for row in source['source']}
    require(len(gates) == 76 and len(old) == 75, 'paid operation count')
    modified = {'residual_first', 'aux_coefficient_root', 'R16', 'strong_square_scaled'}
    retained = [row for row in gates if row[0] not in
                {'residual_first', 'i_square', 'strong_coefficient',
                 'strong_corrected_main', 'strong_square_scaled'}]
    require(retained == [row for row in source['source'] if row[0] not in modified],
            'retained producers changed')
    new = {row[0]: row for row in gates}
    require(new['residual_first'] == ['residual_first', '-', 'norm_first', 1], 'first residual')
    require(new['i_square'] == ['i_square', '*', 'i', 'i'], 'square coefficient')
    require(new['strong_coefficient'] == ['strong_coefficient', '*', 'i_square', 'c2'],
            'factored coefficient')
    require(new['strong_corrected_main'] ==
            ['strong_corrected_main', '+', 'Ac2', 'residual_first'], 'triangular correction')
    require(new['strong_square_scaled'] ==
            ['strong_square_scaled', '*', 'strong_coefficient', 'strong_corrected_main'],
            'corrected scale')

    names = witnesses + ports
    require(len(set(names)) == 19, 'coordinate overlap')
    zero = (0,) * len(names)
    def constant(n): return {zero: n} if n else {}
    def variable(name):
        exponent = list(zero)
        exponent[names.index(name)] = 1
        return {tuple(exponent): 1}
    def power(p, n):
        result = constant(1)
        for _ in range(n): result = multiply(result, p)
        return result
    def weight(exponent): return sum(exponent[:15])

    known = set(names)
    counts = {'+': 0, '-': 0, '*': 0}
    dependencies = {}
    for row in gates:
        require(type(row) is list and len(row) == 4, 'gate format')
        name, op, a, b = row
        require(type(name) is str and name not in known and op in counts, 'gate or operation')
        for operand in (a, b):
            require(type(operand) is int or operand in known, 'forward or invalid operand')
        known.add(name)
        dependencies[name] = (a, b)
        counts[op] += 1
    require(counts == {'+': 19, '-': 16, '*': 41}, 'operation distribution')
    live, stack = set(), [circuit['output']]
    while stack:
        name = stack.pop()
        if type(name) is not str or name in live: continue
        live.add(name)
        stack.extend(dependencies.get(name, ()))
    require(live == known, 'dead gates or unused ports: ' + str(known - live))

    # Fully expand only the small dependency cone of the corrected main factor.
    # This checks the cancellation instead of assuming a leading-form identity.
    exact = {name: variable(name) for name in names}
    def expand(name):
        if type(name) is int: return constant(name)
        if name not in exact:
            _, op, a, b = new[name]
            pa, pb = expand(a), expand(b)
            exact[name] = multiply(pa, pb) if op == '*' else add(pa, pb, 1 if op == '+' else -1)
        return exact[name]
    corrected = expand('strong_corrected_main')
    corrected_degree = max(map(weight, corrected))
    require(corrected_degree == 20, 'corrected factor exact degree')
    corrected_top = {a: c for a, c in corrected.items() if weight(a) == corrected_degree}

    bounds = {name: (1 if name in witnesses else 0, variable(name)) for name in names}
    def operand(value): return (0, constant(value)) if type(value) is int else bounds[value]
    for name, op, a, b in gates:
        da, pa = operand(a)
        db, pb = operand(b)
        if op == '*': degree, top = da + db, multiply(pa, pb)
        else:
            degree = max(da, db)
            top = add(pa if da == degree else {}, pb if db == degree else {}, 1 if op == '+' else -1)
        if name == 'strong_corrected_main':
            require(degree == 22 and not top, 'expected top-degree cancellation')
            degree, top = corrected_degree, corrected_top
        bounds[name] = degree, top
        require(all(weight(a) == degree for a in top), 'homogeneous degree accounting')
    degree, top = bounds[circuit['output']]
    require(degree == 64 and top, 'output exact degree')
    k = add(variable('eta'), variable('zeta'))
    Q = multiply(variable('beta'), variable('J'))
    expected = constant(4)
    for p, n in [(variable('i'), 4), (k, 8), (variable('w'), 2),
                 (variable('s'), 12), (Q, 38)]:
        expected = multiply(expected, power(p, n))
    require(top == expected, 'exact leading homogeneous polynomial')
    witness_exponent = {name: 0 for name in witnesses}
    witness_exponent.update(J=38, i=4, eta=8, w=2, s=12)
    matching = {a: c for a, c in top.items()
                if all(a[j] == witness_exponent[name] for j, name in enumerate(witnesses))}
    beta_exponent = [0] * 19
    for name, exponent in witness_exponent.items(): beta_exponent[names.index(name)] = exponent
    beta_exponent[names.index('beta')] = 38
    require(matching == {tuple(beta_exponent): 4}, 'distinguished nonzero coefficient')
    return {
        'circuit_sha256': hashlib.sha256(CIRCUIT.read_bytes()).hexdigest(),
        'source_sha256': circuit['provenance']['sha256'],
        'operations': 76, 'operation_counts': counts, 'all_gates_and_ports_live': True,
        'positive_witnesses': 15, 'fixed_ports': 4,
        'corrected_main_exact_degree': corrected_degree,
        'corrected_main_expanded_terms': len(corrected),
        'strong_residual_degree': bounds['residual_strong'][0],
        'degree': degree,
        'leading_homogeneous_form': '4*i^4*(eta+zeta)^8*w^2*s^12*(beta*J)^38',
        'distinguished_monomial': 'J^38*i^4*eta^8*w^2*s^12',
        'distinguished_coefficient': '4*beta^38',
        'proof_boundary': circuit['proof_boundary'],
    }


if __name__ == '__main__':
    result = audit()
    LEDGER.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
