"""Independent two-binomial/SOS verification of actual artifacts. CODE ONLY/HOLD."""
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
if hold.get('schema') != 'held_neighbor_gate_shear_finite_v1' or set(hold['files']) != CORE:
    raise ValueError('bootstrap HOLD schema/closure')
for name, expected in hold['files'].items():
    path = HERE / name
    raw = path.read_bytes()
    if path.is_symlink() or {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()} != expected:
        raise ValueError('bootstrap held bytes: ' + name)
spec = importlib.util.spec_from_file_location('neighbor_shear_check_guard', HERE / 'guard.py')
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


def substitute(polynomial, d):
    """Product of two binomial theorems, not factor-by-factor multiplication."""
    result = {}
    for monomial, value in polynomial.items():
        p, q = monomial.count(23), monomial.count(38)
        rest = tuple(i for i in monomial if i not in (23, 38))
        for i in range(p + 1):
            for j in range(q + 1):
                key = tuple(sorted(rest + (22,)*i + (23,)*(p-i)
                                   + (37,)*j + (38,)*(q-j)))
                c = value*comb(p, i)*comb(q, j)*d**(i+j)
                result[key] = result.get(key, 0) + c
    return {m: c for m, c in result.items() if c}


def plus(*polynomials):
    result = {}
    for polynomial in polynomials:
        for m, c in polynomial.items():
            result[m] = result.get(m, 0) + c
    return {m: c for m, c in result.items() if c}


def scale(polynomial, c):
    return {m: c*v for m, v in polynomial.items() if c*v}


def const(c):
    return {(): c} if c else {}


def var(i):
    return {(i,): 1}


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


def ordinary_formulas():
    old, new = {}, {}
    M = linear((2, 10), (4, 11), (2, 21))
    for r, t, v, k, kappa, nu in ((6, 22, 23, 24, 5, 5), (21, 37, 38, 39, 3, 1)):
        A = linear((1, 10), (2, t))
        L = linear((6, 10), (16, t), (2, v))
        P = linear((6, 10), (2, v))
        old[r] = plus(var(t), scale(square_pairs(M), -1), scale(M, -kappa), const(-nu))
        old[r+1] = plus(var(v), scale(square_pairs(A), -1), linear((2, 10), (4, t)), const(-2))
        old[r+2] = plus(var(k), scale(square_pairs(L), -1), L, const(1))
        new[r+1] = plus(var(v), scale(square_pairs(A), -1), linear((2, 10), (-4, t)), const(-2))
        new[r+2] = plus(var(k), scale(square_pairs(P), -1), P, const(1))
    return old, new


def local_tables(t, v, k, kappa, nu):
    # Each triple is (old coefficient, new coefficient, complete monomial).
    cells = [
        (13832, 8, (10, 10, 10, t)), (55320, 24, (10, 10, t, t)),
        (98336, 32, (10, t, t, t)), (65552, 16, (t, t, t, t)),
        (13824, 0, (10, 10, t, v)), (36864, 0, (10, t, t, v)),
        (4608, 0, (10, t, v, v)), (32768, 0, (t, t, t, v)),
        (6144, 0, (t, t, v, v)), (512, 0, (t, v, v, v)),
        (-3488, -16, (10, 10, t)), (-9264, 16, (10, t, t)),
        (-8224, 32, (t, t, t)), (-2312, -8, (10, t, v)),
        (-3080, -8, (t, t, v)), (-384, 0, (t, v, v)),
        (-384, 0, (10, k, t)), (-128, 0, (v, k, t)), (-512, 0, (k, t, t)),
        (-32, -32, (11, 11, t)), (-8, -8, (21, 21, t)),
        (-32, -32, (10, 11, t)), (-16, -16, (10, 21, t)), (-32, -32, (11, 21, t)),
        (-160-4*kappa, -4*kappa, (10, t)), (-8*kappa, -8*kappa, (11, t)),
        (-4*kappa, -4*kappa, (21, t)), (-56, -8, (t, v)),
        (-223, 33, (t, t)), (32, 0, (k, t)), (16-2*nu, 16-2*nu, (t,))]
    before = {tuple(sorted(m)): a for a, b, m in cells if a}
    after = {tuple(sorted(m)): b for a, b, m in cells if b}
    G.need(len(cells) == len(before) == 31 and len(after) == 20, 'ordinary local table schema')
    return before, after


def expected_policy():
    return {'name': 'fixed_neighbor_gate_shear_8_8', 'targets': [23, 38],
            'target_literal_names': ['mul.53', 'mul.148'], 'fixed_inputs': [22, 37],
            'fixed_input_literal_names': ['add.50', 'add.145'],
            'forward_terms': [[[-8, [22]], [1, [23]]], [[-8, [37]], [1, [38]]]],
            'inverse_terms': [[[8, [22]], [1, [23]]], [[8, [37]], [1, [38]]]],
            'all_other_coordinates': 'identity', 'search': False,
            'combined_crt_family_change': False}


def independently_count(equation, rows, polynomial):
    dimension = len(equation['variables'])
    used = sorted(set(i for m in polynomial for i in m))
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


def support_theorem(polynomial, rows, context):
    old = context['collected']
    for t, v, k, kappa, nu in ((22, 23, 24, 5, 5), (37, 38, 39, 3, 1)):
        before, after = local_tables(t, v, k, kappa, nu)
        G.need({m: c for m, c in old.items() if t in m} == before, 'whole old local31 table')
        G.need({m: c for m, c in polynomial.items() if t in m} == after, 'whole actual local20 table')
    G.need({m: c for m, c in old.items() if 22 not in m and 37 not in m} ==
           {m: c for m, c in polynomial.items() if 22 not in m and 37 not in m},
           'all unaffected coefficient identity')
    G.need(set(polynomial) <= set(old) and len(old)-len(polynomial) == 22 and
           all(abs(polynomial.get(m, 0)) <= abs(c) for m, c in old.items()),
           'whole support22/no-growth theorem')
    high = {m: c for m, c in old.items() if abs(c) > 93109}
    G.need(high == {(10, 22, 22, 22): 98336, (10, 37, 37, 37): 98336} and
           polynomial.get((10, 10, 12, 12)) == 93109, 'old height boundary/witness')
    G.need(all(abs(c) <= 160 for i, row in enumerate(context['rows'])
               if i not in (7, 8, 22, 23) for c in row.values()) and
           rows[20].get((10, 12)) == -160 and
           all(abs(c) <= 36 for i in (7, 8, 22, 23) for c in rows[i].values()),
           'row height boundary/witness')
    G.need(sum(len(r) for r in context['rows'])-sum(len(r) for r in rows) == 8,
           'row support8 theorem')
    return {'whole_local_tables': 4, 'old_terms_per_block': 31, 'new_terms_per_block': 20,
            'expanded_terms_removed': 22, 'new_monomials': 0,
            'coefficient_absolute_values_nonincreasing': True,
            'residual_monomial_occurrences_removed': 8}


def prepare(profile):
    old = G.source(profile, 'equation.json')
    n = len(old['variables'])
    G.need(n == (316 if profile == 'plain' else 315) and
           len(old['residuals']) == (218 if profile == 'plain' else 217), 'parent dimension/rows')
    names = [v['name'] for v in old['variables']]
    G.need(len(names) == len(set(names)) and
           [names[i] for i in (10, 11, 12, 21, 22, 23, 24, 37, 38, 39)] ==
           ['crt.encoded.a', 'crt.encoded.b', 'crt.encoded.c', 'mul.40', 'add.50',
            'mul.53', 'add.61', 'add.145', 'mul.148', 'add.156'], 'parent literal names')
    rows = [coefficients(r['terms'], n) for r in old['residuals']]
    oldpoly = G.source(profile, 'expanded_polynomial.json')
    collected = coefficients(oldpoly['terms'], n)
    G.need(sos(rows) == collected, 'parent whole SOS')
    G.need(G.equal(independently_count(old, rows, collected), G.source(profile, 'METRICS.json')),
           'parent complete census')
    occurrences = {str(j): [i for i, row in enumerate(rows) if any(j in m for m in row)]
                   for j in (22, 23, 37, 38)}
    G.need(occurrences == {'22': [6, 7, 8], '23': [7, 8], '37': [21, 22, 23], '38': [22, 23]},
           'whole occurrence closure')
    old_formulas, formulas = ordinary_formulas()
    for i, expected in old_formulas.items():
        G.need(rows[i] == expected, 'ordinary full old residual formula')
    transformed = [substitute(row, -8) for row in rows]
    changed = [i for i, (a, b) in enumerate(zip(rows, transformed)) if a != b]
    G.need(changed == sorted(formulas) == [7, 8, 22, 23], 'complete4 changed-row coverage')
    for i, row in enumerate(transformed):
        G.need(row == (formulas[i] if i in formulas else rows[i]), 'ordinary/unchanged full row')
    whole = sos(transformed)
    G.need(whole == substitute(collected, -8), 'forward whole quartic identity')
    G.need(substitute(whole, 8) == collected, 'inverse whole quartic identity')
    parent = G.source(profile, 'COMPOSED_MAPS.json')
    centered = parent['parent_centered_maps']
    G.need(len(centered['translation']['shifts']) == 58 and
           len(centered['parent_maps']['actual_free_factored_coordinates']) == 83 and
           len(centered['parent_maps']['reverse_monic_restorations']) == (204 if profile == 'plain' else 203),
           'parent whole witness-map counts')
    context = {'old': old, 'rows': rows, 'n': n, 'oldpoly': oldpoly, 'collected': collected,
               'transformed': transformed, 'whole': whole, 'formulas': formulas,
               'changed': changed, 'occurrences': occurrences, 'parent': parent}
    support_theorem(whole, transformed, context)
    return context


def check_index(bundle):
    index = bundle['INDEX.json']
    G.need(index.get('schema') == 'neighbor_gate_shear_data_inventory_v1', 'data index schema')
    G.need(G.equal(index.get('policy'), expected_policy()), 'data index policy')
    expected = {'schema': 'neighbor_gate_shear_data_inventory_v1', 'policy': expected_policy(),
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
    G.need(cert.get('schema') == 'neighbor_gate_shear_v1', 'shear schema')
    G.need(cert.get('convention') == 'balanced_x = neighbor_shear(new_z)', 'shear convention')
    inverse = 'new_z23 = balanced_x23+8balanced_x22; new_z38 = balanced_x38+8balanced_x37'
    G.need(cert.get('inverse_convention') == inverse, 'shear inverse convention')
    policy = cert.get('policy', {})
    G.need(G.equal(policy.get('forward_terms'), expected_policy()['forward_terms']), 'shear direction')
    G.need(G.equal(policy.get('inverse_terms'), expected_policy()['inverse_terms']), 'shear inverse')
    G.need(G.equal(policy, expected_policy()), 'shear policy')
    G.need(G.equal(cert.get('input'), G.source_record(profile, 'equation.json')), 'shear input binding')
    G.need(G.equal(cert.get('changed_rows'), context['changed']), 'shear changed coverage')
    G.need(G.equal(cert.get('complete_occurrences'), context['occurrences']), 'shear occurrence coverage')
    pins = G.obj(HERE / 'SOURCE_PINS.json')
    G.need(G.equal(cert.get('ordinary_proposal'), pins['ordinary_shear_manifest']), 'shear ordinary binding')
    chart = G.record_bytes(G.encode(equation))
    expected_cert = {'schema': 'neighbor_gate_shear_v1', 'profile': profile,
                     'input': G.source_record(profile, 'equation.json'), 'output': chart,
                     'convention': 'balanced_x = neighbor_shear(new_z)', 'inverse_convention': inverse,
                     'policy': expected_policy(), 'changed_rows': context['changed'],
                     'complete_occurrences': context['occurrences'],
                     'ordinary_proposal': pins['ordinary_shear_manifest']}
    G.need(G.equal(cert, expected_cert), 'whole shear certificate')
    oldmeta = {k: v for k, v in old.items() if k != 'residuals'}
    oldmeta['variant'] += ':neighbor_gate_shear_8_8'
    G.need(G.equal({k: v for k, v in equation.items() if k != 'residuals'}, oldmeta), 'equation metadata')
    rawrows = equation.get('residuals')
    G.need(type(rawrows) is list and len(rawrows) == len(context['rows']), 'complete row count')
    rows = []
    for i, (actual, source) in enumerate(zip(rawrows, old['residuals'])):
        G.need(G.equal({k: v for k, v in actual.items() if k != 'terms'},
                       {k: v for k, v in source.items() if k != 'terms'}), 'row metadata')
        row = coefficients(actual['terms'], n)
        G.need(row == context['transformed'][i], 'forward row identity')
        G.need(row == (context['formulas'][i] if i in context['formulas'] else context['rows'][i]),
               'actual ordinary/unchanged residual formula')
        rows.append(row)
    expanded = bundle[pre + 'expanded_polynomial.json']
    G.need(G.equal({k: v for k, v in expanded.items() if k != 'terms'},
                   {k: v for k, v in context['oldpoly'].items() if k != 'terms'}), 'expanded metadata')
    polynomial = coefficients(expanded['terms'], n)
    G.need(polynomial == sos(rows) == context['whole'], 'full SOS coefficient identity')
    G.need(substitute(polynomial, 8) == context['collected'], 'inverse whole quartic identity')
    theorem = support_theorem(polynomial, rows, context)
    metrics = independently_count(equation, rows, polynomial)
    G.need(metrics['degree'] == 4 and metrics['row_degree'] <= 2 and
           metrics['used_coordinates'] == list(range(n)), 'quartic degree/liveness')
    G.need(G.equal(bundle[pre + 'METRICS.json'], metrics), 'complete census')
    G.need(metrics['monomials'] == (5781 if profile == 'plain' else 5787) and
           metrics['height'] == 93109 and metrics['row_height'] == 160,
           'ordinary full support/height deduction')
    parent = context['parent']
    endpoint = G.source(profile, 'ENDPOINT_BINDING.json')
    expected_maps = {
        'schema': 'neighbor_gate_shear_composed_maps_v1', 'profile': profile,
        'chart': chart, 'shear': expected_policy(), 'parent_balanced_maps': parent,
        'parent_balanced_endpoint': endpoint,
        'parent_balanced_shear_certificate': G.source(profile, 'shear_certificate.json'),
        'forward_order': parent['forward_order'] + ['apply_inverse_neighbor_shear_to_balanced_tuple'],
        'inverse_order': ['apply_neighbor_shear_to_recover_balanced_tuple'] + parent['inverse_order'],
        'new_chart_is_whole_integer_bijection': True,
        'old_private_witness_identity_claimed': False, 'source_or_native_program_rerun': False}
    G.need(G.equal(bundle[pre + 'COMPOSED_MAPS.json'], expected_maps), 'complete composed maps')
    expected_endpoint = {
        'schema': 'neighbor_gate_shear_endpoint_v1', 'profile': profile,
        'all_prior_profile_files': {f: G.record_bytes(G.encode(bundle[pre + f]))
                                    for f in G.PROFILE_FILES if f != 'ENDPOINT_BINDING.json'},
        'ordinary_shear_manifest': pins['ordinary_shear_manifest'],
        'accepted_balanced_verification_manifest': pins['accepted_balanced_verification_manifest'],
        'parent_balanced_data_index': G.record(G.SOURCE / 'INDEX.json'),
        'source_calibration': endpoint['source_calibration'],
        'equivalence_chain': ['fixed_neighbor_unimodular_shear'] + endpoint['equivalence_chain'],
        'source_restored_before_calibration': True, 'search_or_optimality_claimed': False}
    G.need(G.equal(bundle[pre + 'ENDPOINT_BINDING.json'], expected_endpoint), 'complete endpoint binding')
    return {'metrics': metrics, 'changed_rows': context['changed'],
            'unchanged_rows': len(rows)-4, 'complete_occurrences': context['occurrences'],
            'whole_forward_and_inverse_coefficients': True, 'ordinary_formulas': 4,
            'support_and_nonincrease_theorem': theorem}


def verify_bundle(bundle, contexts, profiles=('plain', 'weighted')):
    G.need(set(bundle) == G.ARTIFACTS, 'data object inventory')
    check_index(bundle)
    return {p: verify_profile(bundle, p, contexts[p]) for p in profiles}


def rebind(bundle):
    """Rebind actual artifact bytes only; never repair mathematical/source fields."""
    for profile in ('plain', 'weighted'):
        pre = profile + '/'
        chart = G.record_bytes(G.encode(bundle[pre + 'equation.json']))
        bundle[pre + 'shear_certificate.json']['output'] = chart
        bundle[pre + 'COMPOSED_MAPS.json']['chart'] = chart
        bundle[pre + 'ENDPOINT_BINDING.json']['all_prior_profile_files'] = {
            f: G.record_bytes(G.encode(bundle[pre + f]))
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

        add('wrong_direction_first_row', [eq, 'residuals', 7, 'terms'], contexts[profile]['old']['residuals'][7]['terms'], 'forward row identity')
        add('wrong_direction_second_row', [eq, 'residuals', 22, 'terms'], contexts[profile]['old']['residuals'][22]['terms'], 'forward row identity')
        changed = copy.deepcopy(bundle[eq]['residuals'][8]['terms'])
        for term in changed:
            if term[1] == [10, 23]:
                term[0] *= -1
        add('mixed_sign_actual_row', [eq, 'residuals', 8, 'terms'], changed, 'forward row identity')
        changed = copy.deepcopy(bundle[eq]['residuals'][23]['terms'])
        for term in changed:
            term[1] = [36 if i == 38 else i for i in term[1]]
        add('wrong_gate_actual_row', [eq, 'residuals', 23, 'terms'], changed, 'forward row identity')
        add('missing_whole_row', [eq, 'residuals'], bundle[eq]['residuals'][:7]+bundle[eq]['residuals'][8:], 'complete row count')
        add('missing_actual_term', [eq, 'residuals', 8, 'terms'], bundle[eq]['residuals'][8]['terms'][1:], 'forward row identity')
        add('unchanged_row_corruption', [eq, 'residuals', 0, 'terms', 0, 0], 7, 'forward row identity')
        add('preceding_row_corruption', [eq, 'residuals', 6, 'terms', 0, 0], -6, 'forward row identity')
        add('row_label', [eq, 'residuals', 7, 'label'], 'wrong', 'row metadata')
        add('integer_domain', [eq, 'domain'], 'positive integers', 'equation metadata')
        add('literal_name', [eq, 'variables', 23, 'name'], 'mul.54', 'equation metadata')
        add('boolean_coefficient', [eq, 'residuals', 7, 'terms', 0, 0], True, 'integer coefficient')
        add('float_coefficient', [eq, 'residuals', 7, 'terms', 0, 0], -2.0, 'integer coefficient')
        add('boolean_index', [eq, 'residuals', 7, 'terms'], bundle[eq]['residuals'][7]['terms']+[[1, [True]]], 'integer index')
        add('out_of_range_index', [eq, 'residuals', 7, 'terms'], bundle[eq]['residuals'][7]['terms']+[[1, [contexts[profile]['n']]]], 'integer index')
        add('quartic_coefficient', [poly, 'terms', 0, 0], bundle[poly]['terms'][0][0]+1, 'full SOS coefficient identity')
        add('dropped_quartic_term', [poly, 'terms'], bundle[poly]['terms'][1:], 'full SOS coefficient identity')
        add('boolean_quartic_coefficient', [poly, 'terms', 0, 0], True, 'integer coefficient')
        add('quartic_header', [poly, 'domain'], 'positive integers', 'expanded metadata')
        add('certificate_schema', [cert, 'schema'], 'wrong', 'shear schema')
        add('direction_convention', [cert, 'convention'], 'new_z = neighbor_shear(balanced_x)', 'shear convention')
        add('inverse_convention', [cert, 'inverse_convention'], 'new_z = neighbor_shear(balanced_x)', 'shear inverse convention')
        add('first_forward_sign', [cert, 'policy', 'forward_terms', 0, 0, 0], 8, 'shear direction')
        add('second_forward_sign', [cert, 'policy', 'forward_terms', 1, 0, 0], 8, 'shear direction')
        add('inverse_map_sign', [cert, 'policy', 'inverse_terms', 1, 0, 0], -8, 'shear inverse')
        add('wrong_gate_schema', [cert, 'policy', 'targets', 0], 22, 'shear policy')
        add('boolean_gate_schema', [cert, 'policy', 'targets', 0], True, 'shear policy')
        add('stale_input_binding', [cert, 'input', 'sha256'], '0'*64, 'shear input binding')
        add('changed_row_coverage', [cert, 'changed_rows'], contexts[profile]['changed'][1:], 'shear changed coverage')
        add('occurrence_coverage', [cert, 'complete_occurrences', '22'], [7, 8], 'shear occurrence coverage')
        add('ordinary_proof_binding', [cert, 'ordinary_proposal', 'sha256'], '0'*64, 'shear ordinary binding')
        add('inverse_map_order', [maps, 'inverse_order'], list(reversed(bundle[maps]['inverse_order'])), 'complete composed maps')
        nested = ['parent_balanced_maps', 'parent_centered_maps', 'parent_maps']
        free = bundle[maps]['parent_balanced_maps']['parent_centered_maps']['parent_maps']['actual_free_factored_coordinates']
        add('free_coordinate_omission', [maps]+nested+['actual_free_factored_coordinates'], free[1:], 'complete composed maps')
        monic = copy.deepcopy(bundle[maps]['parent_balanced_maps']['parent_centered_maps']['parent_maps']['reverse_monic_restorations'])
        monic[0]['restoration'][0][0] += 1
        add('monic_restoration', [maps]+nested+['reverse_monic_restorations'], monic, 'complete composed maps')
        add('parent_balanced_map_sign', [maps, 'parent_balanced_maps', 'shear', 'forward_terms', 0, 0], 2, 'complete composed maps')
        add('source_calibration', [maps, 'parent_balanced_maps', 'parent_centered_maps', 'source_binding', 'interval_triples_fresh_across_reparameterization'], False, 'complete composed maps')
        add('native_rerun_claim', [maps, 'source_or_native_program_rerun'], True, 'complete composed maps')
        add('whole_height_census', [census, 'height'], bundle[census]['height']+1, 'complete census')
        add('support_census', [census, 'monomials'], bundle[census]['monomials']+1, 'complete census')
        add('row_height_census', [census, 'row_height'], 256, 'complete census')
        add('float_degree_census', [census, 'degree'], 4.0, 'complete census')
        add('endpoint_calibration', [endpoint, 'source_restored_before_calibration'], False, 'complete endpoint binding')
        add('endpoint_parent_binding', [endpoint, 'accepted_balanced_verification_manifest', 'sha256'], '0'*64, 'complete endpoint binding')
        add('index_schema', ['INDEX.json', 'schema'], 'wrong', 'data index schema')
        add('index_search', ['INDEX.json', 'policy', 'search'], True, 'data index policy')
        add('index_combined_family', ['INDEX.json', 'policy', 'combined_crt_family_change'], True, 'data index policy')
        G.need(len(tests) == 46, 'complete negative control coverage')
        for name, mutate, reason in tests:
            actual = copy.deepcopy(bundle)
            mutate(actual)
            rebind(actual)
            try:
                verify_bundle(actual, contexts, (profile,))
            except ValueError as error:
                G.need(str(error) == reason, 'control wrong rejection: '+name+': '+str(error))
            else:
                raise ValueError('control unexpectedly accepted: '+name)
            negatives.append({'profile': profile, 'name': name, 'expected_reason': reason})
        for kind in ('row_reorder', 'row_split_coefficient', 'row_cancel_pair',
                     'quartic_reorder', 'quartic_split_coefficient', 'quartic_cancel_pair'):
            actual = copy.deepcopy(bundle)
            if kind == 'row_reorder':
                actual[eq]['residuals'][7]['terms'].reverse()
            elif kind == 'row_split_coefficient':
                target = actual[eq]['residuals'][8]['terms']
                c, m = target[0]
                target[0] = [c+7, list(m)]
                target.append([-7, list(m)])
            elif kind == 'row_cancel_pair':
                actual[eq]['residuals'][22]['terms'].extend([[9, [10, 37]], [-9, [10, 37]]])
            elif kind == 'quartic_reorder':
                actual[poly]['terms'].reverse()
            elif kind == 'quartic_split_coefficient':
                c, m = actual[poly]['terms'][0]
                actual[poly]['terms'][0] = [c+7, list(m)]
                actual[poly]['terms'].append([-7, list(m)])
            else:
                actual[poly]['terms'].extend([[9, [0, 23, 38]], [-9, [0, 23, 38]]])
            rebind(actual)
            verify_bundle(actual, contexts, (profile,))
            valids.append({'profile': profile, 'name': kind})
    G.need(len(negatives) == 92 and len(valids) == 12, 'complete control counts')
    return {'negative_count': len(negatives), 'valid_count': len(valids),
            'negative_controls': negatives, 'valid_algebraic_controls': valids}


def canonical_terms(bundle, contexts):
    for profile in ('plain', 'weighted'):
        n = contexts[profile]['n']
        for row in bundle[profile+'/equation.json']['residuals']:
            G.need(G.equal(row['terms'], serialized(coefficients(row['terms'], n))), 'canonical saved row terms')
        poly = bundle[profile+'/expanded_polynomial.json']
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
    G.report(receipt, {'schema': 'neighbor_gate_shear_check_result_v1', 'status': 'PASS',
                      'optimize': sys.flags.optimize, 'hold': G.record(HERE/'HOLD_INVENTORY.json'),
                      'artifacts': G.bundle_records(bundle), 'profiles': results, 'controls': evidence,
                      'producer_or_adopted_module_imported': False,
                      'source_or_native_program_rerun': False, 'search': False,
                      'combined_crt_family_change': False})


if __name__ == '__main__':
    main()
