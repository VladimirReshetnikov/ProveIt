#!/usr/bin/env python3
"""Independent endpoint-source audit. Executes no upstream code or giant powers."""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib
import json

ROOT = Path(__file__).resolve().parent
U_PERIOD = 481238074400
X_RESIDUE = 481225262775
V_PERIOD = 576000
Y_RESIDUE = 29948


def bits(n):
    return [i for i in range(n.bit_length()) if (n >> i) & 1]


def add_gate(gates, name, op, a, b):
    gates.append({'out': name, 'op': op, 'args': [a, b]})
    return name


def square_ladder(gates, base, prefix, top):
    p = [base]
    for i in range(1, top + 1):
        p.append(add_gate(gates, f'{prefix}_{i}', 'mul', p[-1], p[-1]))
    return p


def product_chain(gates, operands, prefix):
    assert operands
    cur = operands[0]
    for i, operand in enumerate(operands[1:], 1):
        cur = add_gate(gates, f'{prefix}_{i}', 'mul', cur, operand)
    return cur


def constant_chain(gates):
    xb, ub = set(bits(X_RESIDUE)), set(bits(U_PERIOD))
    common = sorted(xb & ub)
    p = square_ladder(gates, '3', 'ThreeSquare', 38)
    shared = product_chain(gates, [p[i] for i in common], 'ThreeCommon')
    kval = product_chain(gates, [shared] + [p[i] for i in sorted(xb - ub)], 'KBuild')
    uval = product_chain(gates, [shared] + [p[i] for i in sorted(ub - xb)], 'UBuild')
    cval = add_gate(gates, 'CBuild', 'sub', uval, '1')
    return kval, cval, uval


def variable_chain(gates):
    p = square_ladder(gates, 'W', 'WSquare', 19)
    tval = product_chain(gates, [p[i] for i in bits(Y_RESIDUE)], 'TBuild')
    vval = product_chain(gates, [p[i] for i in bits(V_PERIOD)], 'VPowerBuild')
    return tval, vval


def nonpower(gates, kval, cval, tval, vval):
    hx = add_gate(gates, 'Hx', 'sub', 'HxPlus', '1')
    hy = add_gate(gates, 'Hy', 'sub', 'HyPlus', '1')
    cu = add_gate(gates, 'CxHx', 'mul', cval, hx)
    us = add_gate(gates, 'U', 'add', '1', cu)
    dv = add_gate(gates, 'VPowerMinusOne', 'sub', vval, '1')
    dhy = add_gate(gates, 'VIncrement', 'mul', dv, hy)
    vs = add_gate(gates, 'V', 'add', '1', dhy)
    ac = add_gate(gates, 'Acol', 'mul', kval, us)
    add_gate(gates, 'ColumnBound', 'add', ac, 'BoundCol')
    at = add_gate(gates, 'AT', 'mul', ac, tval)
    add_gate(gates, 'EndpointHead', 'mul', at, vs)


def make_source(paid):
    gates = []
    if paid:
        kval, cval, uval = constant_chain(gates)
        constant_end = len(gates)
    else:
        kval, cval, uval = 'K', 'C', None
        constant_end = 0
    tval, vval = variable_chain(gates)
    variable_end = len(gates)
    nonpower(gates, kval, cval, tval, vval)
    return {
        'model': 'paid_constant_construction' if paid else 'free_fixed_numeral_ports',
        'literal_ports': ['1', '3'] if paid else ['1'],
        'fixed_numeral_recipes': {} if paid else {
            'K': {'base': 3, 'exponent': X_RESIDUE},
            'C': {'base': 3, 'exponent': U_PERIOD, 'subtract': 1},
        },
        'existing_relation_ports': ['W', 'FinalHead', 'FinalSignPlus'],
        'new_positive_witnesses': ['HxPlus', 'HyPlus', 'BoundCol'],
        'gates': gates,
        'equalities': [['ColumnBound', 'W'], ['EndpointHead', 'FinalHead'], ['FinalSignPlus', '1']],
        'section_ends': [constant_end, variable_end, len(gates)],
        'power_targets': {'K': kval, 'ThreeToU': uval, 'T': tval, 'WToV': vval},
    }


def ledger(gates):
    c = Counter(g['op'] for g in gates)
    return {'M': c['mul'], 'A': c['add'] + c['sub'], 'total': len(gates)}


def check_source(source):
    # Symbolic exponent bookkeeping only. Never evaluate 3**X_RESIDUE.
    known = set(source['literal_ports']) | set(source['fixed_numeral_recipes'])
    known |= set(source['existing_relation_ports']) | set(source['new_positive_witnesses'])
    powers = {'3': ('three', 1), 'W': ('W', 1)}
    if source['fixed_numeral_recipes']:
        powers['K'] = ('three', X_RESIDUE)
    for g in source['gates']:
        assert g['out'] not in known
        assert all(a in known for a in g['args'])
        known.add(g['out'])
        a, b = g['args']
        if g['op'] == 'mul' and a in powers and b in powers and powers[a][0] == powers[b][0]:
            powers[g['out']] = (powers[a][0], powers[a][1] + powers[b][1])
    targets = source['power_targets']
    assert powers[targets['K']] == ('three', X_RESIDUE)
    if targets['ThreeToU']:
        assert powers[targets['ThreeToU']] == ('three', U_PERIOD)
    assert powers[targets['T']] == ('W', Y_RESIDUE)
    assert powers[targets['WToV']] == ('W', V_PERIOD)
    assert all(a in known and b in known for a, b in source['equalities'])
    a, b, c = source['section_ends']
    return {
        'constant_construction': ledger(source['gates'][:a]),
        'variable_powers': ledger(source['gates'][a:b]),
        'nonpower': ledger(source['gates'][b:c]),
        'total': ledger(source['gates']),
        'power_exponents_verified': True,
        'acyclic_and_all_inputs_defined': True,
    }


def small_domain_regression():
    # Bounded arithmetic regression of the selector theorem, separate from the
    # ant-history proof. Enumerate witnesses via factors forced by a prime-power
    # endpoint, then check the original arithmetic equations directly.
    cases = accepted = zero_hx = zero_hy = 0
    for u, v in product([2, 4, 6], repeat=2):
        for x0 in range(1, u, 2):
            for y0 in range(0, v, 2):
                for w in [3, 5, 7, 9]:
                    W = 3**w
                    for h in [2, 4, 6, 8]:
                        for j in range(w*h):
                            x, y = j % w, j // w
                            want = (x % u == x0 and y % v == y0)
                            solutions = []
                            remaining = j - x0 - w*y0
                            for a in range(max(-1, remaining)+1):
                                b = remaining-a
                                if b < 0:
                                    continue
                                ua, vb = 3**a, 3**b
                                if (ua-1) % (3**u-1) or (vb-1) % (W**v-1):
                                    continue
                                Hx = (ua-1)//(3**u-1)
                                Hy = (vb-1)//(W**v-1)
                                Acol = 3**x0 * (1+(3**u-1)*Hx)
                                BoundCol = W-Acol
                                endpoint = Acol * W**y0 * (1+(W**v-1)*Hy)
                                if BoundCol > 0 and endpoint == 3**j:
                                    solutions.append((Hx, Hy, BoundCol))
                            assert bool(solutions) == want, (u, v, x0, y0, w, h, j, solutions)
                            assert len(solutions) <= 1
                            if want:
                                assert (x+y)%2 == 1
                                accepted += 1
                                zero_hx += solutions[0][0] == 0
                                zero_hy += solutions[0][1] == 0
                            cases += 1
    # Explicit false positive if the strict column bound is dropped.
    u, v, x0, y0, w, j = 2, 2, 1, 0, 3, 5
    W, Hx, Hy = 3**w, 10, 0
    Acol = 3**x0 * (1+(3**u-1)*Hx)
    assert Acol * W**y0 * (1+(W**v-1)*Hy) == 3**j
    assert (j % w, j//w) == (2, 1)
    assert Acol >= W
    return {'tested_endpoints': cases, 'accepted_endpoints': accepted,
            'accepted_Hx_zero': zero_hx, 'accepted_Hy_zero': zero_hy,
            'bound_omission_counterexample_verified': True}


def main():
    assert 0 <= X_RESIDUE < U_PERIOD and 0 <= Y_RESIDUE < V_PERIOD
    assert U_PERIOD%2 == V_PERIOD%2 == 0 and X_RESIDUE%2 == 1 and Y_RESIDUE%2 == 0
    sources = {label: make_source(paid) for label, paid in [('fixed_numerals', False), ('paid_numerals', True)]}
    audits = {k: check_source(v) for k, v in sources.items()}
    assert audits['fixed_numerals']['total'] == {'M': 37, 'A': 6, 'total': 43}
    assert audits['paid_numerals']['total'] == {'M': 94, 'A': 7, 'total': 101}
    for label, source in sources.items():
        (ROOT / f'endpoint_{label}_source.json').write_text(json.dumps(source, indent=2)+'\n')
    report = {
        'constants': {'u': U_PERIOD, 'x0': X_RESIDUE, 'v': V_PERIOD, 'y0': Y_RESIDUE},
        'bit_positions': {
            'x0': bits(X_RESIDUE), 'u': bits(U_PERIOD),
            'shared_x0_u': sorted(set(bits(X_RESIDUE)) & set(bits(U_PERIOD))),
            'y0': bits(Y_RESIDUE), 'v': bits(V_PERIOD),
        },
        'audits': audits,
        'small_domain_regression': small_domain_regression(),
        'upstream_code_executed': False,
        'giant_fixed_powers_materialized': False,
        'scope': 'Endpoint selector only; no raw-input compiler, periodic background, or final polynomial combination.',
    }
    files = ['audit_endpoint.py', 'endpoint_fixed_numerals_source.json', 'endpoint_paid_numerals_source.json']
    report['sha256'] = {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in files}
    (ROOT/'endpoint_audit_receipt.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
