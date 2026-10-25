"""Independent multinomial/symmetric-pair verification. CODE ONLY/HOLD."""
import argparse
import copy
import hashlib
import importlib.util
import json
from math import comb
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CORE = {'README.md', 'PROOF.md', 'TOOLCHAIN.md', 'guard.py', 'build.py',
        'check.py', 'SOURCE_PINS.json'}
hold = json.loads((HERE / 'HOLD_INVENTORY.json').read_text())
if hold.get('schema') != 'held_balanced_crt_shear_finite_v1' or set(hold['files']) != CORE:
    raise ValueError('bootstrap HOLD schema/closure')
for name, expected in hold['files'].items():
    path = HERE / name
    raw = path.read_bytes()
    if path.is_symlink() or {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()} != expected:
        raise ValueError('bootstrap held bytes: ' + name)
spec = importlib.util.spec_from_file_location('balanced_shear_check_guard', HERE / 'guard.py')
G = importlib.util.module_from_spec(spec)
spec.loader.exec_module(G)


def coefficients(raw, dimension):
    G.need(type(raw) is list, 'term list type')
    result = {}
    for pair in raw:
        G.need(type(pair) is list and len(pair) == 2, 'term pair shape')
        c, monomial = pair
        G.need(type(c) is int, 'integer coefficient')
        G.need(type(monomial) is list, 'monomial list type')
        G.need(all(type(i) is int and 0 <= i < dimension for i in monomial),
               'integer index')
        key = tuple(sorted(monomial))
        result[key] = result.get(key, 0) + c
    return {m: c for m, c in result.items() if c != 0}


def serialized(polynomial):
    return [[polynomial[m], list(m)] for m in sorted(polynomial)]


def substitute(polynomial, coefficient):
    """Expand (u+coefficient*a+coefficient*b)^k by its multinomial theorem."""
    result = {}
    for monomial, value in polynomial.items():
        k = monomial.count(21)
        rest = tuple(i for i in monomial if i != 21)
        for a_power in range(k + 1):
            for b_power in range(k - a_power + 1):
                u_power = k - a_power - b_power
                key = tuple(sorted(rest + (10,)*a_power + (11,)*b_power + (21,)*u_power))
                c = value*comb(k, a_power)*comb(k-a_power, b_power)*coefficient**(a_power+b_power)
                result[key] = result.get(key, 0) + c
    return {m: c for m, c in result.items() if c}


def plus(*polynomials):
    result = {}
    for polynomial in polynomials:
        for m, c in polynomial.items():
            result[m] = result.get(m, 0) + c
    return {m: c for m, c in result.items() if c}


def scale(polynomial, coefficient):
    return {m: coefficient*c for m, c in polynomial.items() if coefficient*c}


def const(value):
    return {(): value} if value else {}


def var(index):
    return {(index,): 1}


def linear(*pairs):
    return plus(*(scale(var(i), c) for c, i in pairs))


def square_pairs(polynomial):
    result = {}
    entries = sorted(polynomial.items())
    for i, (m, c) in enumerate(entries):
        for j in range(i, len(entries)):
            n, d = entries[j]
            key = tuple(sorted((*m, *n)))
            result[key] = result.get(key, 0) + c*d*(1 if i == j else 2)
    return {m: c for m, c in result.items() if c}


def sos(rows):
    result = {}
    for row in rows:
        for m, c in square_pairs(row).items():
            result[m] = result.get(m, 0) + c
    return {m: c for m, c in result.items() if c}


def product_by_variable(polynomial, index):
    return {tuple(sorted((*m, index))): c for m, c in polynomial.items()}


def ordinary_formulas(profile):
    a, b, c, u = (var(i) for i in (10, 11, 12, 21))
    M = linear((2, 10), (4, 11), (2, 21))
    L12 = linear((8, 10), (4, 11), (8, 12), (2, 21), (2, 27))
    L15 = linear((2, 10), (4, 11), (4, 12), (2, 21), (4, 27), (2, 30))
    L19 = linear((-2, 10), (-4, 11), (2, 12), (2, 21), (2, 25))
    L50 = linear((-2, 10), (-4, 11), (1, 12), (2, 21))
    L51 = linear((-2, 10), (-4, 11), (2, 21), (2, 66))
    L52 = linear((-4, 10), (-8, 11), (4, 21), (2, 65), (2, 67))
    rows = {
        5: plus(u, scale(square_pairs(plus(a, b)), -1), const(-1)),
        6: plus(var(22), scale(square_pairs(M), -1), scale(M, -5), const(-5)),
        12: plus(var(28), scale(square_pairs(L12), -1), scale(M, -1)),
        15: plus(var(31), scale(square_pairs(L15), -1), scale(L15, 2), scale(M, -1), const(1)),
        19: plus(var(35), scale(square_pairs(L19), -1), scale(L19, 8), const(-12)),
        21: plus(var(37), scale(square_pairs(M), -1), scale(M, -3), const(-1)),
        25: plus(var(41), scale(square_pairs(u), -16), scale(u, -14), scale(a, -2), scale(b, -4), const(-6)),
        50: plus(var(66), scale(square_pairs(L50), -1), scale(L50, -2), c),
        51: plus(var(67), scale(square_pairs(L51), -1), scale(L51, 2), const(1)),
        52: plus(var(68), scale(square_pairs(L52), -1), scale(L52, -1), scale(var(65), 2), const(-2))}
    r1, o1, r2, o2, r3, o3 = ((71, 86, 73, 89, 90, 105) if profile == 'plain'
                              else (71, 87, 74, 90, 91, 106))
    rows[r1] = plus(var(o1), const(-1), scale(var(3), 2),
                    scale(product_by_variable(plus(u, scale(a, -1), scale(b, -2)), 3), -2))
    rows[r2] = plus(var(o2), const(-1), scale(product_by_variable(M, 3), -1))
    D = linear(*((v, i) for i, v in ((24, 2), (26, 4), (29, 2), (31, 2), (32, 4),
                                    (34, 2), (36, 2), (39, 4), (40, 2), (43, 2),
                                    (47, 2), (68, 4), (69, 2))))
    rows[r3] = plus(var(o3), scale(a, -1), scale(b, -1), scale(u, -4), scale(D, -1))
    return rows


def expected_policy():
    return {'name': 'balanced_crt_gate_shear_2_2', 'target': 21,
            'target_literal_name': 'mul.40', 'input_names':
            ['crt.encoded.a', 'crt.encoded.b'], 'input_indices': [10, 11],
            'forward_terms': [[-2, [10]], [-2, [11]], [1, [21]]],
            'inverse_terms': [[2, [10]], [2, [11]], [1, [21]]],
            'all_other_coordinates': 'identity', 'search': False}


def independently_count(equation, rows, polynomial):
    dimension = len(equation['variables'])
    used = sorted(set(i for monomial in polynomial for i in monomial))
    degrees = {}
    for degree in sorted(set(map(len, polynomial))):
        values = [c for m, c in polynomial.items() if len(m) == degree]
        degrees[str(degree)] = {'terms': len(values), 'height': max(abs(c) for c in values)}
    return {'variables': dimension, 'rows': len(rows), 'degree': max(map(len, polynomial), default=0),
            'monomials': len(polynomial), 'height': max((abs(c) for c in polynomial.values()), default=0),
            'row_height': max((abs(c) for row in rows for c in row.values()), default=0),
            'row_degree': max((len(m) for row in rows for m in row), default=0),
            'used_coordinates': used, 'unconstrained_coordinates': [i for i in range(dimension) if i not in used],
            'degree_census': degrees}


def prepare(profile):
    old = G.source(profile, 'equation.json')
    n = len(old['variables'])
    G.need(n == (316 if profile == 'plain' else 315), 'parent dimension')
    names = [v['name'] for v in old['variables']]
    G.need(len(names) == len(set(names)) and
           [names[i] for i in (10, 11, 12, 21)] ==
           ['crt.encoded.a', 'crt.encoded.b', 'crt.encoded.c', 'mul.40'], 'parent literal names')
    rows = [coefficients(r['terms'], n) for r in old['residuals']]
    oldpoly = G.source(profile, 'expanded_polynomial.json')
    collected = coefficients(oldpoly['terms'], n)
    G.need(sos(rows) == collected, 'parent whole SOS')
    transformed = [substitute(r, -2) for r in rows]
    formulas = ordinary_formulas(profile)
    occurrence = [i for i, r in enumerate(rows) if any(21 in m for m in r)]
    changed = [i for i, (x, y) in enumerate(zip(rows, transformed)) if x != y]
    G.need(occurrence == sorted(formulas) == changed and len(changed) == 13,
           'complete13 changed-row coverage')
    for i, expected in formulas.items():
        G.need(transformed[i] == expected, 'ordinary full residual formula')
    whole = sos(transformed)
    G.need(whole == substitute(collected, -2), 'forward whole quartic identity')
    G.need(substitute(whole, 2) == collected, 'inverse whole quartic identity')
    parent = G.source(profile, 'COMPOSED_MAPS.json')
    G.need(len(parent['translation']['shifts']) == 58 and
           len(parent['parent_maps']['actual_free_factored_coordinates']) == 83 and
           len(parent['parent_maps']['reverse_monic_restorations']) == (204 if profile == 'plain' else 203),
           'parent whole witness-map counts')
    return {'old': old, 'rows': rows, 'n': n, 'oldpoly': oldpoly, 'collected': collected,
            'transformed': transformed, 'whole': whole, 'formulas': formulas,
            'changed': changed, 'parent': parent}


def check_index(bundle):
    index = bundle['INDEX.json']
    G.need(index.get('schema') == 'balanced_crt_gate_shear_data_inventory_v1', 'data index schema')
    G.need(G.equal(index.get('policy'), expected_policy()), 'data index policy')
    expected = {'schema': 'balanced_crt_gate_shear_data_inventory_v1', 'policy': expected_policy(),
                'files': G.bundle_records({k: v for k, v in bundle.items() if k != 'INDEX.json'}),
                'source_pins': G.record(HERE / 'SOURCE_PINS.json'),
                'producer': G.record(HERE / 'build.py'), 'checker': G.record(HERE / 'check.py'),
                'guard': G.record(HERE / 'guard.py')}
    G.need(G.equal(index, expected), 'whole data index binding')


def verify_profile(bundle, profile, context):
    pre = profile + '/'
    old, n = context['old'], context['n']
    equation = bundle[pre + 'equation.json']
    cert = bundle[pre + 'shear_certificate.json']
    G.need(cert.get('schema') == 'balanced_crt_gate_shear_v1', 'shear schema')
    G.need(cert.get('convention') == 'centered_x = shear(new_z)', 'shear convention')
    G.need(cert.get('inverse_convention') == 'new_z21 = centered_x21+2centered_x10+2centered_x11',
           'shear inverse convention')
    policy = cert.get('policy', {})
    G.need(G.equal(policy.get('forward_terms'), expected_policy()['forward_terms']), 'shear direction')
    G.need(G.equal(policy.get('inverse_terms'), expected_policy()['inverse_terms']), 'shear inverse')
    G.need(G.equal(policy, expected_policy()), 'shear policy')
    G.need(G.equal(cert.get('input'), G.source_record(profile, 'equation.json')), 'shear input binding')
    G.need(G.equal(cert.get('changed_rows'), context['changed']), 'shear changed coverage')
    chart = G.record_bytes(G.encode(equation))
    expected_cert = {'schema': 'balanced_crt_gate_shear_v1', 'profile': profile,
                     'input': G.source_record(profile, 'equation.json'), 'output': chart,
                     'convention': 'centered_x = shear(new_z)',
                     'inverse_convention': 'new_z21 = centered_x21+2centered_x10+2centered_x11',
                     'policy': expected_policy(), 'changed_rows': context['changed']}
    G.need(G.equal(cert, expected_cert), 'whole shear certificate')
    oldmeta = {k: v for k, v in old.items() if k != 'residuals'}
    oldmeta['variant'] += ':balanced_crt_gate_shear_2_2'
    G.need(G.equal({k: v for k, v in equation.items() if k != 'residuals'}, oldmeta), 'equation metadata')
    rawrows = equation.get('residuals')
    G.need(type(rawrows) is list and len(rawrows) == len(context['rows']), 'complete row count')
    rows = []
    for i, (actual, source) in enumerate(zip(rawrows, old['residuals'])):
        G.need(G.equal({k: v for k, v in actual.items() if k != 'terms'},
                       {k: v for k, v in source.items() if k != 'terms'}), 'row metadata')
        row = coefficients(actual['terms'], n)
        G.need(row == context['transformed'][i], 'forward row identity')
        if i in context['formulas']:
            G.need(row == context['formulas'][i], 'actual ordinary residual formula')
        else:
            G.need(row == context['rows'][i], 'unchanged-row identity')
        rows.append(row)
    expanded = bundle[pre + 'expanded_polynomial.json']
    G.need(G.equal({k: v for k, v in expanded.items() if k != 'terms'},
                   {k: v for k, v in context['oldpoly'].items() if k != 'terms'}), 'expanded metadata')
    polynomial = coefficients(expanded['terms'], n)
    G.need(polynomial == sos(rows) == context['whole'], 'full SOS coefficient identity')
    G.need(substitute(polynomial, 2) == context['collected'], 'inverse whole quartic identity')
    metrics = independently_count(equation, rows, polynomial)
    G.need(metrics['degree'] == 4 and metrics['row_degree'] <= 2 and
           metrics['used_coordinates'] == list(range(n)), 'quartic degree/liveness')
    G.need(G.equal(bundle[pre + 'METRICS.json'], metrics), 'complete census')
    chosen = {(10, 10, 11, 12): 28798, (10, 10, 12, 12): 93109,
              (10, 10, 11, 11): 15158 if profile == 'plain' else 15157,
              (10, 11, 11, 11): 14300, (10, 10, 11, 21): 0,
              (10, 22, 22, 22): 98336, (10, 37, 37, 37): 98336}
    G.need(all(polynomial.get(m, 0) == c for m, c in chosen.items()) and metrics['height'] >= 98336,
           'selected coefficient theorem/bound')
    parent = context['parent']
    expected_maps = {'schema': 'balanced_crt_gate_shear_composed_maps_v1',
                     'profile': profile, 'chart': chart, 'shear': expected_policy(),
                     'parent_centered_maps': parent,
                     'parent_centered_endpoint': G.source(profile, 'ENDPOINT_BINDING.json'),
                     'parent_translation_certificate': G.source(profile, 'translation_certificate.json'),
                     'forward_order': parent['forward_order'] + ['apply_inverse_shear_to_centered_tuple'],
                     'inverse_order': ['apply_shear_to_recover_centered_tuple'] + parent['inverse_order'],
                     'new_chart_is_whole_integer_bijection': True,
                     'old_private_witness_identity_claimed': False, 'source_or_native_program_rerun': False}
    G.need(G.equal(bundle[pre + 'COMPOSED_MAPS.json'], expected_maps), 'complete composed maps')
    pins = G.obj(HERE / 'SOURCE_PINS.json')
    expected_endpoint = {
        'schema': 'balanced_crt_gate_shear_endpoint_v1', 'profile': profile,
        'all_prior_profile_files': {f: G.record_bytes(G.encode(bundle[pre + f]))
                                    for f in G.PROFILE_FILES if f != 'ENDPOINT_BINDING.json'},
        'ordinary_shear_manifest': pins['ordinary_shear_manifest'],
        'accepted_centered_verification_manifest': pins['accepted_centered_verification_manifest'],
        'parent_centered_data_index': G.record(G.SOURCE / 'INDEX.json'),
        'source_calibration': parent['source_binding'],
        'equivalence_chain': ['fixed_unimodular_shear', 'fixed58_translation',
                              'accepted_raw_free_monic_Horn_maps', 'whole_source_ordinary_calibration'],
        'source_restored_before_calibration': True, 'search_or_optimality_claimed': False}
    G.need(G.equal(bundle[pre + 'ENDPOINT_BINDING.json'], expected_endpoint), 'complete endpoint binding')
    return {'metrics': metrics, 'changed_rows': context['changed'],
            'unchanged_rows': len(rows)-13, 'whole_forward_and_inverse_coefficients': True,
            'ordinary_formulas': 13, 'selected_coefficient_identities': 7}


def verify_bundle(bundle, contexts, profiles=('plain', 'weighted')):
    G.need(set(bundle) == G.ARTIFACTS, 'data object inventory')
    check_index(bundle)
    return {p: verify_profile(bundle, p, contexts[p]) for p in profiles}


def rebind(bundle):
    """Rebind only actual artifact byte hashes, never mathematical/map payloads."""
    for profile in ('plain', 'weighted'):
        prefix = profile + '/'
        chart = G.record_bytes(G.encode(bundle[prefix + 'equation.json']))
        bundle[prefix + 'shear_certificate.json']['output'] = chart
        bundle[prefix + 'COMPOSED_MAPS.json']['chart'] = chart
        bundle[prefix + 'ENDPOINT_BINDING.json']['all_prior_profile_files'] = {
            f: G.record_bytes(G.encode(bundle[prefix + f]))
            for f in G.PROFILE_FILES if f != 'ENDPOINT_BINDING.json'}
    bundle['INDEX.json']['files'] = G.bundle_records({k: v for k, v in bundle.items() if k != 'INDEX.json'})


def put(root, path, value):
    for part in path[:-1]:
        root = root[part]
    root[path[-1]] = value


def controls(bundle, contexts):
    negatives, valids = [], []
    for profile in ('plain', 'weighted'):
        pre = profile + '/'
        eq, poly, cert, maps, census, endpoint = (pre + f for f in
            ('equation.json', 'expanded_polynomial.json', 'shear_certificate.json',
             'COMPOSED_MAPS.json', 'METRICS.json', 'ENDPOINT_BINDING.json'))
        tests = []

        def add(name, path, value, reason):
            tests.append((name, lambda b, p=path, v=value: put(b, p, copy.deepcopy(v)), reason))

        add('wrong_direction_actual_row', [eq, 'residuals', 5, 'terms'], contexts[profile]['old']['residuals'][5]['terms'], 'forward row identity')
        changed = copy.deepcopy(bundle[eq]['residuals'][6]['terms'])
        for term in changed:
            if term[1] == [10, 21]:
                term[0] *= -1
        add('wrong_sign_actual_row', [eq, 'residuals', 6, 'terms'], changed, 'forward row identity')
        changed = copy.deepcopy(bundle[eq]['residuals'][25]['terms'])
        for term in changed:
            term[1] = [20 if i == 21 else i for i in term[1]]
        add('wrong_gate_actual_row', [eq, 'residuals', 25, 'terms'], changed, 'forward row identity')
        add('missing_whole_row', [eq, 'residuals'], bundle[eq]['residuals'][:5] + bundle[eq]['residuals'][6:], 'complete row count')
        add('missing_actual_term', [eq, 'residuals', 5, 'terms'], bundle[eq]['residuals'][5]['terms'][1:], 'forward row identity')
        add('unchanged_row_corruption', [eq, 'residuals', 0, 'terms', 0, 0], 7, 'forward row identity')
        add('row_label', [eq, 'residuals', 5, 'label'], 'wrong', 'row metadata')
        add('integer_domain', [eq, 'domain'], 'positive integers', 'equation metadata')
        add('literal_name', [eq, 'variables', 21, 'name'], 'mul.41', 'equation metadata')
        add('boolean_coefficient', [eq, 'residuals', 5, 'terms', 0, 0], True, 'integer coefficient')
        add('float_coefficient', [eq, 'residuals', 5, 'terms', 0, 0], -1.0, 'integer coefficient')
        changed = copy.deepcopy(bundle[eq]['residuals'][5]['terms'])
        changed.append([1, [True]])
        add('boolean_index', [eq, 'residuals', 5, 'terms'], changed, 'integer index')
        add('quartic_coefficient', [poly, 'terms', 0, 0], bundle[poly]['terms'][0][0] + 1, 'full SOS coefficient identity')
        add('dropped_quartic_term', [poly, 'terms'], bundle[poly]['terms'][1:], 'full SOS coefficient identity')
        add('quartic_header', [poly, 'domain'], 'positive integers', 'expanded metadata')
        add('certificate_schema', [cert, 'schema'], 'wrong', 'shear schema')
        add('certificate_direction_convention', [cert, 'convention'], 'new_z = shear(centered_x)', 'shear convention')
        add('certificate_inverse_convention', [cert, 'inverse_convention'], 'new_z21 = centered_x21-2centered_x10-2centered_x11', 'shear inverse convention')
        add('forward_map_sign', [cert, 'policy', 'forward_terms', 0, 0], 2, 'shear direction')
        add('inverse_map_sign', [cert, 'policy', 'inverse_terms', 0, 0], -2, 'shear inverse')
        add('wrong_gate_schema', [cert, 'policy', 'target'], 20, 'shear policy')
        add('boolean_gate_schema', [cert, 'policy', 'target'], True, 'shear policy')
        add('stale_input_binding', [cert, 'input', 'sha256'], '0'*64, 'shear input binding')
        add('changed_row_coverage', [cert, 'changed_rows'], contexts[profile]['changed'][1:], 'shear changed coverage')
        add('inverse_map_order', [maps, 'inverse_order'], list(reversed(bundle[maps]['inverse_order'])), 'complete composed maps')
        free = bundle[maps]['parent_centered_maps']['parent_maps']['actual_free_factored_coordinates']
        add('free_coordinate_omission', [maps, 'parent_centered_maps', 'parent_maps', 'actual_free_factored_coordinates'], free[1:], 'complete composed maps')
        monic = copy.deepcopy(bundle[maps]['parent_centered_maps']['parent_maps']['reverse_monic_restorations'])
        monic[0]['restoration'][0][0] += 1
        add('monic_restoration', [maps, 'parent_centered_maps', 'parent_maps', 'reverse_monic_restorations'], monic, 'complete composed maps')
        add('source_calibration', [maps, 'parent_centered_maps', 'source_binding', 'interval_triples_fresh_across_reparameterization'], False, 'complete composed maps')
        add('whole_height_census', [census, 'height'], bundle[census]['height'] + 1, 'complete census')
        add('float_degree_census', [census, 'degree'], 4.0, 'complete census')
        add('endpoint_calibration', [endpoint, 'source_restored_before_calibration'], False, 'complete endpoint binding')
        add('index_schema', ['INDEX.json', 'schema'], 'wrong', 'data index schema')
        add('index_search', ['INDEX.json', 'policy', 'search'], True, 'data index policy')
        G.need(len(tests) == 33, 'complete negative control coverage')
        for name, mutate, reason in tests:
            actual = copy.deepcopy(bundle)
            mutate(actual)
            rebind(actual)
            try:
                verify_bundle(actual, contexts, (profile,))
            except ValueError as error:
                G.need(str(error) == reason, 'control wrong rejection: ' + name + ': ' + str(error))
            else:
                raise ValueError('control unexpectedly accepted: ' + name)
            negatives.append({'profile': profile, 'name': name, 'expected_reason': reason})
        for kind in ('row_reorder', 'row_split_coefficient', 'quartic_reorder', 'quartic_cancel_pair'):
            actual = copy.deepcopy(bundle)
            if kind == 'row_reorder':
                actual[eq]['residuals'][5]['terms'].reverse()
            elif kind == 'row_split_coefficient':
                target = actual[eq]['residuals'][6]['terms']
                c, m = target[0]
                target[0] = [c+7, list(m)]
                target.append([-7, list(m)])
            elif kind == 'quartic_reorder':
                actual[poly]['terms'].reverse()
            else:
                actual[poly]['terms'].extend([[9, [0, 21]], [-9, [0, 21]]])
            rebind(actual)
            verify_bundle(actual, contexts, (profile,))
            valids.append({'profile': profile, 'name': kind})
    G.need(len(negatives) == 66 and len(valids) == 8, 'complete control counts')
    return {'negative_count': len(negatives), 'valid_count': len(valids),
            'negative_controls': negatives, 'valid_algebraic_controls': valids}


def canonical_terms(bundle, contexts):
    for profile in ('plain', 'weighted'):
        n = contexts[profile]['n']
        equation = bundle[profile + '/equation.json']
        for row in equation['residuals']:
            G.need(G.equal(row['terms'], serialized(coefficients(row['terms'], n))), 'canonical saved row terms')
        poly = bundle[profile + '/expanded_polynomial.json']
        G.need(G.equal(poly['terms'], serialized(coefficients(poly['terms'], n))), 'canonical saved polynomial terms')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--data', required=True)
    parser.add_argument('--receipt', required=True)
    args = parser.parse_args()
    G.authenticate()
    G.need(sys.flags.optimize in (0, 1), 'optimize mode')
    data = G.external_data(args.data, absent=False)
    receipt = G.external_receipt(args.receipt, 'check-optimized' if sys.flags.optimize else 'check')
    bundle = G.read_bundle(data)
    contexts = {p: prepare(p) for p in ('plain', 'weighted')}
    results = verify_bundle(bundle, contexts)
    canonical_terms(bundle, contexts)
    evidence = controls(bundle, contexts)
    G.authenticate()
    G.report(receipt, {'schema': 'balanced_crt_gate_shear_check_result_v1', 'status': 'PASS',
                      'optimize': sys.flags.optimize, 'hold': G.record(HERE / 'HOLD_INVENTORY.json'),
                      'artifacts': G.bundle_records(bundle), 'profiles': results, 'controls': evidence,
                      'producer_or_adopted_module_imported': False,
                      'source_or_native_program_rerun': False, 'search': False})


if __name__ == '__main__':
    main()
