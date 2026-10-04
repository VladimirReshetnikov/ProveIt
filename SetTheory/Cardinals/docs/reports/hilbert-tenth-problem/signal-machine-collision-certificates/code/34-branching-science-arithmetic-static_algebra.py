#!/usr/bin/env python3
"""Fresh static polynomial checks for Report 65.

This expands declared equations and evaluates manually declared witnesses.
It contains no native-machine interpreter, signal simulation, or schedule search.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
# Manually declared graph: state 0 tests/decrements A; state 1 increments B;
# state 2 is halt. Edges: A-zero, A-positive, B-increment, virtual halt.
EDGES = [
    {'source': 0, 'target': 2, 'da': 0, 'db': 0, 'zero': 'A'},
    {'source': 0, 'target': 1, 'da': -1, 'db': 0, 'zero': None},
    {'source': 1, 'target': 0, 'da': 0, 'db': 1, 'zero': None},
    {'source': 2, 'target': 2, 'da': 0, 'db': 0, 'zero': None},
]
E, Z, Q0, HALT, HALT_EDGE = 4, 1, 0, 2, 3


def p_add(a, b):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + c
        if out[m] == 0:
            del out[m]
    return out


def p_scale(c, a):
    assert isinstance(c, int)
    return {m: c * d for m, d in a.items() if c * d}


def p_sub(a, b):
    return p_add(a, p_scale(-1, b))


def p_mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x + y for x, y in zip(ma, mb))
            out[m] = out.get(m, 0) + ca * cb
            if out[m] == 0:
                del out[m]
    return out


def p_sum(polynomials):
    out = {}
    for p in polynomials:
        out = p_add(out, p)
    return out


def degree(p):
    return max((sum(m) for m in p), default=-1)


def evaluate(p, values):
    total = 0
    for m, c in p.items():
        term = c
        for v, power in zip(values, m):
            term *= v ** power
        total += term
    return total


def build(T):
    assert T >= 1
    names = ['A', 'B']
    for t in range(T):
        names += [f'w_{t}_{e}' for e in range(E)]
        names += [f'A_{t+1}', f'B_{t+1}']
    n = len(names)
    index = {name: i for i, name in enumerate(names)}
    assert len(index) == n
    zero_monomial = (0,) * n

    def const(c):
        return {zero_monomial: c} if c else {}

    def var(name):
        monomial = [0] * n
        monomial[index[name]] = 1
        return {tuple(monomial): 1}

    one, two = const(1), const(2)
    w = [[var(f'w_{t}_{e}') for e in range(E)] for t in range(T)]
    s = [[p_sub(v, one) for v in ws] for ws in w]
    A = [var('A')] + [var(f'A_{t}') for t in range(1, T+1)]
    B = [var('B')] + [var(f'B_{t}') for t in range(1, T+1)]
    residuals = []
    labels = []

    def add_residual(name, p):
        labels.append(name)
        residuals.append(p)

    def weighted(field, selectors):
        return p_sum(p_scale(edge[field], selector)
                     for edge, selector in zip(EDGES, selectors))

    for t in range(T):
        for e in range(E):
            add_residual(f'selector_{t}_{e}', p_mul(p_sub(w[t][e], one),
                                                   p_sub(w[t][e], two)))
        add_residual(f'one_hot_{t}', p_sub(p_sum(s[t]), one))
        add_residual(f'update_A_{t}', p_sub(p_sub(A[t+1], A[t]), weighted('da', s[t])))
        add_residual(f'update_B_{t}', p_sub(p_sub(B[t+1], B[t]), weighted('db', s[t])))
        for e, edge in enumerate(EDGES):
            if edge['zero'] is not None:
                counter = A[t] if edge['zero'] == 'A' else B[t]
                add_residual(f'zero_{t}_{e}', p_mul(s[t][e], p_sub(counter, one)))
    add_residual('initial_control', p_sub(weighted('source', s[0]), const(Q0)))
    for t in range(T-1):
        add_residual(f'control_link_{t}', p_sub(weighted('target', s[t]),
                                               weighted('source', s[t+1])))
    add_residual('final_control', p_sub(weighted('target', s[-1]), const(HALT)))
    assert len(residuals) == T * (E + Z + 4) + 1
    assert len(names) - 2 == T * (E + 2)
    assert all(degree(r) <= 2 for r in residuals)
    polynomial = p_sum(p_mul(r, r) for r in residuals)
    early = p_sum(s[t][HALT_EDGE] for t in range(T))
    exact = p_add(polynomial, p_mul(early, early))
    assert degree(polynomial) == degree(exact) == 4
    assert all(isinstance(c, int) for c in polynomial.values())
    used = {i for monomial in polynomial for i, power in enumerate(monomial) if power}
    assert len(used) == len(names)
    for t in range(T):
        for e in range(E):
            m = [0] * n
            m[index[f'w_{t}_{e}']] = 4
            assert polynomial.get(tuple(m)) == 1
            assert exact.get(tuple(m)) == 1
    return {'names': names, 'index': index, 'residuals': residuals, 'labels': labels,
            'polynomial': polynomial, 'exact': exact,
            'ledger': {'horizon': T, 'edges': E, 'zero_edges': Z,
                       'positive_inputs': 2, 'positive_witnesses': n-2,
                       'residuals': len(residuals), 'exact_halt_residuals': len(residuals)+1,
                       'degree': degree(polynomial), 'expanded_monomials': len(polynomial),
                       'pure_selector_fourth_power_coefficients': 1}}


def manual_fixture(T, data):
    # These rows are explicitly supplied trace data, not produced by execution.
    declared_rows = [(1, 1, 1), (2, 1, 2), (0, 1, 2), (3, 1, 2)]
    assert T in (3, 4)
    values = [2, 1]  # Native counters initially (1,0), shifted positive.
    for selected, a, b in declared_rows[:T]:
        values += [2 if e == selected else 1 for e in range(E)] + [a, b]
    assert len(values) == len(data['names']) and all(v > 0 for v in values)
    residual_values = [evaluate(r, values) for r in data['residuals']]
    assert all(v == 0 for v in residual_values)
    assert evaluate(data['polynomial'], values) == 0
    exact_value = evaluate(data['exact'], values)
    assert exact_value == (0 if T == 3 else 1)
    wrong = list(values)
    wrong[data['index']['w_0_0']] = 2  # Illegally choose both outgoing edges.
    wrong_value = evaluate(data['polynomial'], wrong)
    assert wrong_value > 0
    return {'horizon': T, 'inputs': values[:2], 'positive_witness': values[2:],
            'all_residuals_zero': True, 'by_horizon_polynomial': 0,
            'first_halt_exact_polynomial': exact_value,
            'two_selected_edges_polynomial': wrong_value}


result = {'kind': 'static integer polynomial certificate',
          'native_interpreter_executed': False, 'physical_simulator_executed': False,
          'declared_edges': EDGES, 'ledgers': [], 'fixtures': []}
for T in (1, 2, 3, 4):
    data = build(T)
    result['ledgers'].append(data['ledger'])
    if T in (3, 4):
        result['fixtures'].append(manual_fixture(T, data))
result['checker_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
out = ROOT / 'evidence' / 'static_checks.json'
out.write_text(json.dumps(result, indent=2) + '\n')
print('PASS: exact polynomial ledgers, quartic coefficients, and declared positive trace fixtures')
print(out)
