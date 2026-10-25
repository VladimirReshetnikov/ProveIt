"""Fixed two-neighbor shear, using factor multiplication. CODE ONLY/HOLD."""
import argparse
import copy
import hashlib
import importlib.util
import json
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
spec = importlib.util.spec_from_file_location('neighbor_shear_build_guard', HERE / 'guard.py')
G = importlib.util.module_from_spec(spec)
spec.loader.exec_module(G)


def add(*values):
    out = {}
    for value in values:
        for m, c in value.items():
            out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def mul(left, right):
    out = {}
    for m, c in left.items():
        for n, d in right.items():
            key = tuple(sorted(m + n))
            out[key] = out.get(key, 0) + c*d
    return {m: c for m, c in out.items() if c}


def norm(terms):
    return add(*({tuple(sorted(m)): c} for c, m in terms))


def terms(value):
    return [[c, list(m)] for m, c in sorted(value.items())]


def shear(value):
    replacements = {23: {(22,): -8, (23,): 1},
                    38: {(37,): -8, (38,): 1}}
    out = {}
    for m, c in value.items():
        product = {(): c}
        for j in m:
            product = mul(product, replacements.get(j, {(j,): 1}))
        out = add(out, product)
    return out


def census(equation, polynomial):
    rows = [norm(r['terms']) for r in equation['residuals']]
    used = sorted({j for m in polynomial for j in m})
    degrees = {}
    for m, c in polynomial.items():
        cell = degrees.setdefault(str(len(m)), {'terms': 0, 'height': 0})
        cell['terms'] += 1
        cell['height'] = max(cell['height'], abs(c))
    return {'variables': len(equation['variables']), 'rows': len(rows),
            'degree': max(map(len, polynomial), default=0),
            'monomials': len(polynomial),
            'height': max(map(abs, polynomial.values()), default=0),
            'row_height': max((abs(c) for row in rows for c in row.values()), default=0),
            'row_degree': max((len(m) for row in rows for m in row), default=0),
            'used_coordinates': used,
            'unconstrained_coordinates': sorted(set(range(len(equation['variables']))) - set(used)),
            'degree_census': degrees}


def policy():
    return {'name': 'fixed_neighbor_gate_shear_8_8', 'targets': [23, 38],
            'target_literal_names': ['mul.53', 'mul.148'], 'fixed_inputs': [22, 37],
            'fixed_input_literal_names': ['add.50', 'add.145'],
            'forward_terms': [[[-8, [22]], [1, [23]]], [[-8, [37]], [1, [38]]]],
            'inverse_terms': [[[8, [22]], [1, [23]]], [[8, [37]], [1, [38]]]],
            'all_other_coordinates': 'identity', 'search': False,
            'combined_crt_family_change': False}


def produce():
    bundle = {}
    pins = G.obj(HERE / 'SOURCE_PINS.json')
    for profile in ('plain', 'weighted'):
        prefix = profile + '/'
        old = G.source(profile, 'equation.json')
        equation = copy.deepcopy(old)
        for row in equation['residuals']:
            row['terms'] = terms(shear(norm(row['terms'])))
        equation['variant'] += ':neighbor_gate_shear_8_8'
        bundle[prefix + 'equation.json'] = equation
        polynomial = {}
        for row in equation['residuals']:
            value = norm(row['terms'])
            polynomial = add(polynomial, mul(value, value))
        expanded = copy.deepcopy(G.source(profile, 'expanded_polynomial.json'))
        expanded['terms'] = terms(polynomial)
        bundle[prefix + 'expanded_polynomial.json'] = expanded
        bundle[prefix + 'METRICS.json'] = census(equation, polynomial)
        chart = G.record_bytes(G.encode(equation))
        changed = [i for i, (a, b) in enumerate(zip(old['residuals'], equation['residuals']))
                   if norm(a['terms']) != norm(b['terms'])]
        occurrences = {str(j): [i for i, row in enumerate(old['residuals'])
                               if any(j in m for c, m in row['terms'])]
                       for j in (22, 23, 37, 38)}
        bundle[prefix + 'shear_certificate.json'] = {
            'schema': 'neighbor_gate_shear_v1', 'profile': profile,
            'input': G.source_record(profile, 'equation.json'), 'output': chart,
            'convention': 'balanced_x = neighbor_shear(new_z)',
            'inverse_convention': 'new_z23 = balanced_x23+8balanced_x22; new_z38 = balanced_x38+8balanced_x37',
            'policy': policy(), 'changed_rows': changed, 'complete_occurrences': occurrences,
            'ordinary_proposal': pins['ordinary_shear_manifest']}
        parent = G.source(profile, 'COMPOSED_MAPS.json')
        endpoint = G.source(profile, 'ENDPOINT_BINDING.json')
        bundle[prefix + 'COMPOSED_MAPS.json'] = {
            'schema': 'neighbor_gate_shear_composed_maps_v1', 'profile': profile,
            'chart': chart, 'shear': policy(), 'parent_balanced_maps': parent,
            'parent_balanced_endpoint': endpoint,
            'parent_balanced_shear_certificate': G.source(profile, 'shear_certificate.json'),
            'forward_order': parent['forward_order'] + ['apply_inverse_neighbor_shear_to_balanced_tuple'],
            'inverse_order': ['apply_neighbor_shear_to_recover_balanced_tuple'] + parent['inverse_order'],
            'new_chart_is_whole_integer_bijection': True,
            'old_private_witness_identity_claimed': False,
            'source_or_native_program_rerun': False}
        prior = {name: G.record_bytes(G.encode(bundle[prefix + name]))
                 for name in G.PROFILE_FILES if name != 'ENDPOINT_BINDING.json'}
        bundle[prefix + 'ENDPOINT_BINDING.json'] = {
            'schema': 'neighbor_gate_shear_endpoint_v1', 'profile': profile,
            'all_prior_profile_files': prior,
            'ordinary_shear_manifest': pins['ordinary_shear_manifest'],
            'accepted_balanced_verification_manifest': pins['accepted_balanced_verification_manifest'],
            'parent_balanced_data_index': G.record(G.SOURCE / 'INDEX.json'),
            'source_calibration': endpoint['source_calibration'],
            'equivalence_chain': ['fixed_neighbor_unimodular_shear'] + endpoint['equivalence_chain'],
            'source_restored_before_calibration': True, 'search_or_optimality_claimed': False}
    bundle['INDEX.json'] = {
        'schema': 'neighbor_gate_shear_data_inventory_v1', 'policy': policy(),
        'files': G.bundle_records(bundle), 'source_pins': G.record(HERE / 'SOURCE_PINS.json'),
        'producer': G.record(HERE / 'build.py'), 'checker': G.record(HERE / 'check.py'),
        'guard': G.record(HERE / 'guard.py')}
    return bundle


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--data', required=True)
    parser.add_argument('--receipt', required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    G.authenticate()
    G.need(sys.flags.optimize in (0, 1), 'optimize mode')
    G.need(args.check or not sys.flags.optimize, 'materialization requires normal mode')
    role = ('rebuild-optimized' if sys.flags.optimize else 'rebuild') if args.check else 'build'
    data = G.external_data(args.data, absent=not args.check)
    receipt = G.external_receipt(args.receipt, role)
    bundle = produce()
    if args.check:
        G.need(G.equal(G.read_bundle(data), bundle), 'pure rebuild whole data bytes')
    G.authenticate()
    if not args.check:
        G.save_bundle(data, bundle)
    G.need(G.equal(G.read_bundle(data), bundle), 'whole written/read data identity')
    G.authenticate()
    G.report(receipt, {'schema': 'neighbor_gate_shear_build_result_v1',
                      'status': 'PASS', 'role': role, 'optimize': sys.flags.optimize,
                      'hold': G.record(HERE / 'HOLD_INVENTORY.json'),
                      'artifacts': G.bundle_records(bundle),
                      'metrics': {p: bundle[p + '/METRICS.json'] for p in ('plain', 'weighted')},
                      'search': False, 'combined_crt_family_change': False,
                      'source_or_native_program_rerun': False})


if __name__ == '__main__':
    main()
