#!/usr/bin/env python3
"""Safe norm units and two strong normalizations for the dyadic recoder.

The joined duration test is retained literally.  Seven-factor projection
has a positive coordinate bijection; the optional two new strong units
instead use positive embedding and fresh canonical auxiliary extensions.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import native_binary_dyadic_duration_recoder as raw
import native_binary_input_dilation_unit179 as units
import pcp_normalized_strong_history_units as single
import complete75_normalized_strong87 as canonical

execute = raw.execute
PREFIXES = ('geo__', 'and__')


def scalar(value, env):
    return env[value] if isinstance(value, str) else value


def rewrite(old, *, normalize_strong=True):
    assert old.get('dyadic_duration') and old.get('fused_paddings')
    rows = {row[0]: row for row in old['source']}
    critical = {
        'joint16B': ('*', 16, 'B'),
        'and__q': ('*', 'joint16B', 'scale'),
        'joint16duration': ('*', 16, 'duration'),
        'and__scaled_A': ('*', 'joint16B', 'copies'),
        'joint_A_sum': ('+', 'and__scaled_A', 'joint16duration'),
        'and__padded_A': ('+', 'joint_A_sum', 12),
        'and__scaled_B': ('*', 'joint16B', 'K'),
        'joint_B_sum': ('+', 'and__scaled_B', 'joint16duration'),
        'and__padded_B': ('-', 'joint_B_sum', 6),
        'and__scaled_Z': ('*', 'joint16B', 'Ahat'),
        'joint_Z_difference': ('-', 'and__scaled_Z', 'joint16B'),
        'and__F3': ('+', 'joint_Z_difference', 8),
        'duration_J': ('+', 'duration_multiple', 'duration'),
        'duration_bound': ('+', 'duration', 'duration_slack'),
    }
    assert all(rows[n][1:] == r for n, r in critical.items())
    assert old['comparisons'][-2:] == [('duration_J', 'J'), ('duration_bound', 'Bm1')]
    base = units.rewrite(old)
    assert base['unit_factors'].count('and__bs_q') == 1
    assert len(base['unit_factors']) == 7
    assert base['equations'] == old['equations'] - 19
    assert base['witnesses'] == old['witnesses'] - 13
    p = dict(base)
    if normalize_strong:
        rebuilt = {prefix + n for prefix in PREFIXES for n in ('f', 'i', 'j', 'o', 'y_aux')}
        deps = {n: {n} for n in base['parameters'] + base['auxiliaries']}
        dep = lambda v: deps[v] if isinstance(v, str) else set()
        for n, _, a, b in base['source']:
            deps[n] = dep(a) | dep(b)
        exceptions = {(p + 'ic22', p + 'R16') for p in PREFIXES}
        exceptions |= {(p + 'H17', p + 'aux_u_rhs') for p in PREFIXES}
        for a, b in base['comparisons'][:-1]:
            if (a, b) not in exceptions:
                assert not (dep(a) | dep(b)) & rebuilt
        for name in base['unit_factors']:
            if name not in {p + 'P17' for p in PREFIXES}:
                assert not deps[name] & rebuilt
        for prefix in PREFIXES:
            p = single.rewrite(dict(p, core_prefix=prefix, scale_exponent=1))
        for key in ('exact_degree', 'alternative_SOS_degree', 'normalized_strong_factor',
                    'removed_strong_comparison', 'core_prefix', 'scale_exponent'):
            p.pop(key, None)
    p.update(raw_parent=old, unit_parent=base, parent_packet=base, normalize_strong=normalize_strong,
             normalized_strong_factors=[p + 'f_square_minus_one' for p in PREFIXES]
             if normalize_strong else [],
             removed_strong_comparisons=[(p + 'ic22', p + 'R16') for p in PREFIXES]
             if normalize_strong else [])
    assert p['equations'] == old['equations'] - (21 if normalize_strong else 19)
    assert p['operations'] == old['operations'] + (10 if normalize_strong else 6)
    assert p['auxiliaries'] == base['auxiliaries']
    assert p['unit_factors'].count('and__bs_q') == 1
    assert ('duration_J', 'J') in p['comparisons'][:-1]
    assert ('duration_bound', 'Bm1') in p['comparisons'][:-1]
    actual_names = {row[0] for row in p['source']} | set(p['parameters'] + p['auxiliaries'])
    assert all(n in actual_names for n in p['public_registers'].values())
    return p


def build(width=2, *, normalize_strong=True):
    return rewrite(raw.build(width), normalize_strong=normalize_strong)


def polynomial_source(packet, *, sum_of_squares=False):
    return units.polynomial_source(packet, sum_of_squares=sum_of_squares)


def lift_to_unit_parent(packet, values):
    if not packet['normalize_strong']:
        return dict(values)
    env = execute(packet['source'], values)
    return dict(values, **{p + 'i': env[p + 'A'] * values[p + 'i'] for p in PREFIXES})


def lift_to_raw(packet, values):
    return units.lift(packet['unit_parent'], lift_to_unit_parent(packet, values))


def audit_identity(packet, values):
    base = packet['unit_parent']
    lifted = lift_to_unit_parent(packet, values)
    units.audit_identity(packet['raw_parent'], base, lifted)
    env = execute(packet['source'], values)
    before = execute(base['source'], lifted)
    corrected = {}
    if packet['normalize_strong']:
        for p in PREFIXES:
            Delta, N = env[p + 'A'], env[p + 'f_square_minus_one']
            residual = before[p + 'ic22'] - before[p + 'R16']
            assert residual == Delta * (1 - N)
            corrected[p + 'P17'] = before[p + 'P17'] + residual * env[p + 'aux_square_gap']
            assert corrected[p + 'P17'] == env[p + 'P17']
            corrected[p + 'f_square_minus_one'] = N
    for name in base['unit_factors']:
        if name not in corrected:
            assert env[name] == before[name]
            corrected[name] = before[name]
    removed = set(packet['removed_strong_comparisons'])
    residuals = [scalar(a, before) - scalar(b, before)
                 for a, b in base['comparisons'][:-1] if (a, b) not in removed]
    assert residuals == [scalar(a, env) - scalar(b, env) for a, b in packet['comparisons'][:-1]]
    product = 1
    for name in packet['unit_factors']:
        product *= corrected[name]
    assert env[packet['unit_register']] == product
    source, out = polynomial_source(packet)
    assert execute(source, values)[out] == product * (1 + sum(r * r for r in residuals)) - 1
    # Crucially, normalized-coordinate changes do not touch any joined port.
    for name in ('Q', 'modulus', 'duration_J', 'duration_bound', 'and__q',
                 'and__padded_A', 'and__padded_B', 'and__F3', 'and__bs_packed', 'and__bs_q'):
        assert env[name] == before[name]
    if all(v > 0 for v in values.values()):
        assert all(v > 0 for v in lift_to_raw(packet, values).values())
        assert env['input_bound'] >= 2 and env['repunit_P'] > 0 and env['and__F3'] >= 8


def degree_audit(packet, input_degree=1, *, exact=False):
    """Actual DAG propagation, with both algebraic main-norm cancellations."""
    assert input_degree in (1, 2)
    names = packet['parameters'] + packet['auxiliaries']
    degree = {n: 1 for n in names}
    degree['x'] = input_degree
    top = {n: 1 + j % 3 for j, n in enumerate(names)}
    for p in PREFIXES:
        top[p + 'tau_gap'] = 1
        top[p + 'eta'] = top[p + 'zeta'] = 1
    d = lambda v: degree[v] if isinstance(v, str) else 0
    c = lambda v: top[v] if isinstance(v, str) else v
    rows = {n: (op, a, b) for n, op, a, b in packet['source']}
    for name, op, a, b in packet['source']:
        da, db = d(a), d(b)
        if op == '*':
            degree[name], top[name] = da + db, c(a) * c(b)
        else:
            degree[name] = max(da, db)
            ca, cb = (c(a) if da == degree[name] else 0), (c(b) if db == degree[name] else 0)
            top[name] = ca + cb if op == '+' else ca - cb
        for p in PREFIXES:
            if name != p + 'R15':
                continue
            X, ac, G, aa, cc = (p + n for n in ('wn2', 'cam2', 'gam', 'R12', 'R10a'))
            expected = {p + 'R15': ('-', p + 'L15', p + 'Ac2'),
                        p + 'R14': ('+', p + 'D1', G), p + 'D1': ('+', X, ac),
                        ac: ('*', cc, aa), G: ('*', p + 'ga', p + 'a4m5'),
                        p + 'a4m5': ('+', p + 'a4', 3), p + 'a4': ('*', 4, aa),
                        p + 'A': ('+', p + 'a_square', p + 'a4m5'),
                        p + 'a_square': ('*', aa, aa), p + 'c2': ('*', cc, cc),
                        p + 'Ac2': ('*', p + 'A', p + 'c2'),
                        p + 'L15': ('*', p + 'R14', p + 'R14')}
            assert all(rows[n] == row for n, row in expected.items())
            high = d(ac) + d(G)
            assert high > max(2 * d(X), d(X) + d(ac), d(X) + d(G), 2 * d(G),
                              d(p + 'a4m5') + 2 * d(cc))
            degree[name], top[name] = high, 2 * c(ac) * c(G)
    k, e = packet['width'], input_degree
    v = (2 * k + 1) * e + 1
    assert d('input_bound') == e and d('B') == k * e
    assert d('repunit_P') == k * e + 1 and d('and__q') == v
    assert d('and__F3') == k * e + 1
    assert d('and__bs_packed') == 3 * v + k * e + 1
    expected = {}
    for p, z in [('geo__', e), ('and__', v)]:
        expected[p + 'R15'] = 5 * z + 7
        expected[p + 'first_unit'] = 3 * z + 5
        a, cc, U, i = (c(p + n) for n in ('R12', 'R10a', 'H17', 'i'))
        assert c(p + 'R15') == 8 * c(p + 'ga') * a * a * cc
        expected_aux = ((14 * e + 24 if p == 'geo__' else 18 * v + 2 * k * e + 20)
                        if packet['normalize_strong'] else
                        (6 * e + 12 if p == 'geo__' else 10 * v + 2 * k * e + 8))
        expected[p + 'P17'] = expected_aux
        if packet['normalize_strong']:
            expected[p + 'f_square_minus_one'] = 8 * z + 14
            assert c(p + 'P17') == a ** 4 * i * i * cc ** 4 * U * U
            assert c(p + 'f_square_minus_one') == -a * a * i * i * cc ** 4
        else:
            assert c(p + 'P17') == a * a * c(p + 'f') ** 2 * U * U
    expected['and__bs_q'] = v
    assert {n: d(n) for n in packet['unit_factors']} == expected
    residuals = []
    for a, b in packet['comparisons'][:-1]:
        high = max(d(a), d(b))
        coefficient = (c(a) if d(a) == high else 0) - (c(b) if d(b) == high else 0)
        residuals.append((a, b, high, coefficient))
    maximum = max(r[2] for r in residuals)
    outer = sum(r[3] ** 2 for r in residuals if r[2] == maximum)
    if packet['normalize_strong']:
        assert maximum == 3 * v + k * e + 1
        assert outer == 6 * c('and__bs_packed') ** 2
        product_degree = 30 * e + 35 * v + 2 * k * e + 96
        result_degree = (86 * k + 71) * e + 139
    else:
        assert maximum == 4 * v + 10
        assert outer == (c('and__i') ** 2 * c('and__R10a') ** 4) ** 2
        product_degree = 14 * e + 19 * v + 2 * k * e + 44
        result_degree = (56 * k + 41) * e + 91
    assert d(packet['unit_register']) == product_degree
    assert product_degree + 2 * maximum == result_degree
    coefficient = c(packet['unit_register']) * outer
    assert coefficient
    hashed = hashlib.sha256(hex(int(coefficient)).encode()).hexdigest()
    answer = dict(input_degree=e, AND_scale_degree=v, AND_output_field_degree=k * e + 1,
                  unit_degree=product_degree, maximum_outer_degree=maximum,
                  exact_degree=result_degree, alternative_SOS_degree=2 * max(product_degree, maximum),
                  factor_degrees=expected,
                  maximum_outer_residuals=[[a, b, d] for a, b, d, _ in residuals if d == maximum],
                  leading_coefficient_sha256=hashed,
                  main_norm_cancellation_prerequisites_checked=True)
    if exact:
        T = sp.Symbol('T')
        values = {n: sp.Poly(top[n] * T ** (e if n == 'x' else 1) + j + 1, T)
                  for j, n in enumerate(names)}
        products = {n for n, _, _, _ in packet['source']
                    if n.startswith('recoder_unit_product') or n.endswith('normalized_all_units')}
        source = [r for r in packet['source'] if r[0] not in products]
        env = execute(source, values)
        fs = [sp.Poly(env[n], T) for n in packet['unit_factors']]
        rs = [sp.Poly(scalar(a, env) - scalar(b, env), T) for a, b in packet['comparisons'][:-1]]
        assert {n: f.degree() for n, f in zip(packet['unit_factors'], fs)} == expected
        assert max(r.degree() for r in rs) == maximum
        actual = sum(r.LC() ** 2 for r in rs if r.degree() == maximum)
        for f in fs:
            actual *= f.LC()
        assert actual == coefficient
        answer['exact_weighted_polynomial_audit'] = True
    return answer


def ledger(packet):
    source, out = polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert len(source) == packet['operations'] + 3 * packet['equations'] - 1
    return dict(width=packet['width'], normalize_strong=packet['normalize_strong'],
                certificate=dict(operations=packet['operations'], multiplications=packet['multiplications'],
                                 additions_subtractions=packet['additions_subtractions']),
                witnesses=packet['witnesses'], equations=packet['equations'],
                polynomial=dict(operations=len(source), multiplications=counts['M'],
                                additions_subtractions=counts['A'], output=out),
                degree=degree_audit(packet))


def verify():
    rng = random.Random(19139382)
    records = []
    identities = signed = exact = 0
    for width in (2, 3, 4, 8, 16, 64, 160):
        for normalize in (False, True):
            packet = build(width, normalize_strong=normalize)
            if width == 2:
                json.dumps(packet)  # Both returned metadata graphs must be acyclic.
            record = ledger(packet)
            for case in range(48):
                values = {n: rng.randrange(1, 7) if case < 24 else rng.randrange(-3, 5)
                          for n in packet['parameters'] + packet['auxiliaries']}
                audit_identity(packet, values)
                identities += 1
                signed += case >= 24
            for input_degree in (1, 2):
                actual = width in (2, 3, 4)
                audit = degree_audit(packet, input_degree, exact=actual)
                record['degree' if input_degree == 1 else 'quadratic_loaded_input_degree'] = audit
                exact += actual
            records.append(record)
    base = ledger(build())
    assert base['certificate'] == dict(operations=147, multiplications=78, additions_subtractions=69)
    assert base['equations'] == 15 and base['witnesses'] == 39
    assert base['polynomial']['operations'] == 191
    assert (base['polynomial']['multiplications'], base['polynomial']['additions_subtractions']) == (93, 98)
    assert base['degree']['exact_degree'] == 382
    unnormalized = ledger(build(normalize_strong=False))
    assert unnormalized['polynomial']['operations'] == 193
    assert unnormalized['degree']['exact_degree'] == 244
    # Independent local canonical divisibility fixtures; not full recoder zeros.
    canonical_cases = [canonical.canonical(A, J) for A, J in ((2, 3), (3, 3), (4, 3), (2, 7))]
    packet = build()
    source, out = polynomial_source(packet)
    return dict(status='PASS_NATIVE_BINARY_DYADIC_DURATION_UNITS', ledgers=records,
                checks=dict(full_signed_correction_and_output_identities=identities,
                            signed_cases=signed, exact_factor_and_outer_polynomial_audits=exact,
                            canonical_auxiliary_cases=canonical_cases,
                            full_native_Pell_zeros_materialized=False),
                example=dict(parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                             source=packet['source'], comparisons=packet['comparisons'],
                             polynomial_finalizer=source[packet['operations']:], output=out,
                             unit_factors=packet['unit_factors']),
                scope='Same complete ordinary-input dyadic-duration relation as the137 recoder. '
                      'No universal tag composition or universal operation bound is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2) + '\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
