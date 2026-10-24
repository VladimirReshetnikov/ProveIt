#!/usr/bin/env python3
"""Retain raw coefficients, derive A/D bounds, and free private comparisons."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
CONFIGS = [('retained', 0, None), ('support2_affine1', 2, 1),
           ('support2_affine2', 2, 2), ('support4_affine2', 4, 2), ('support8_affine2', 8, 2)]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def digest(raw):
    return sha256(raw).hexdigest()


def load(name):
    return json.loads((HERE / name).read_text())


def dependencies(step):
    return set() if step['kind'] == 'affine_square' else {
        i for c, m in step['rhs'] for i, n in Counter(m).items() if n % 2}


def closure(known, original):
    steps = []
    while True:
        changed = False
        for step in original:
            if step['variable'] not in known and dependencies(step) <= known:
                known.add(step['variable'])
                steps.append(step)
                changed = True
        if not changed:
            return steps


def generate():
    pins = load('SOURCE_PINS.json')
    for name, pin in pins['sources'].items():
        need(digest((HERE / 'source' / name).read_bytes()) == pin['sha256'], 'immutable input ' + name)
    source = load('source/raw_natural.json')
    raw = load('source/raw_builder.json')
    old = load('source/old_raw_domain.json')['positivity']
    routes = load('source/route_natural667.json')
    route_sign = load('source/route_sign.json')
    identities = {encoded(v): i for i, v in enumerate(source['variables'])}
    mapped = {identities[encoded(routes['variables'][v])] for v in route_sign['guards']}
    seeds = mapped - {644, 917}
    omitted = {identities[encoded(routes['variables'][v])] for v in route_sign['removed_guards']}
    need(len(mapped) == 109 and len(seeds) == 107 and len(omitted) == 52, 'full raw identity mapping')
    need(seeds | omitted | {644, 917} == set(old['guard_indices']), 'exact original161 seed partition')
    bounds = load('source/four_bounds.json')
    known = seeds | {step['variable'] for step in bounds}
    steps = closure(known, old['proof_steps'])
    need(len(steps) == 976 and len(known) == 1087, 'initial complete107-seed sign closure')
    initial = set(known)
    # Old sign selection used B=A+U*bq. The actual retained definition
    # B=1+x666 is independently available before bq has a sign.
    base_row = next(i for i, r in enumerate(raw['rows']) if r.get('gate') == 667)
    base_bound = dict(variable=667, lower=1, factor=[[1, []]], rhs=[[1, []], [1, [666]]],
                      row_combination=[dict(row=base_row, multiplier=[[1, []]])])
    known.add(667)
    late = {i for i in omitted if re.fullmatch(r'pow\d+\.quotient|shared_index\.Bquotient',
                                               source['variables'][i]['name'])}
    known.update(late)
    later_steps = closure(known, old['proof_steps'])
    need(len(late) == 22 and len(later_steps) == 29 and len(known) == 1139, 'late orientation closure')
    unknown = set(range(1259)) - initial
    sr = {i for i in unknown if re.fullmatch(r'index\d+\.(S|R)', source['variables'][i]['name'])}
    private_gates = unknown - omitted - sr
    need((len(unknown), len(sr), len(private_gates)) == (172, 30, 90), 'complete signed-private boundary')
    certificate = dict(schema='raw107_mixed_domain_bounds_and_signs_v1',
        seed_indices=sorted(seeds), mapped_route_guard_indices=sorted(mapped),
        omitted_quotient_indices=sorted(omitted), omitted_bound_indices=[644, 917],
        bound_steps=bounds, sign_steps=steps, known_after_initial_steps=sorted(initial),
        early_comparison_base_bound=base_bound,
        unresolved=dict(quotients=sorted(omitted), comparison_coordinates=sorted(sr), private_gates=sorted(private_gates)),
        late_semantic_quotients=sorted(late), late_sign_steps=later_steps,
        known_after_late_orientations=sorted(known))
    interface = deepcopy(load('source/route_interfaces.json'))
    interface['schema'] = 'raw107_complete_private_interface_v1'
    interface.pop('raw_nonnegative_from_initial_sign_steps')
    interface['nonnegative_raw_before_index_recovery'] = sorted(initial | {667})
    interface['source_raw_variables'] = 1259
    interface['source_raw_rows'] = 1177
    signed = deepcopy(source)
    signed['domain'] = 'unrestricted integers'
    signed['variant'] = 'retained_raw_mixed107_derived_A_D'
    signed.pop('metrics', None)
    guards = []
    for j, v in enumerate(sorted(seeds)):
        a, b, c = range(1259 + 3*j, 1259 + 3*j + 3)
        signed['variables'].extend({'kind': 'integer_guard', 'name': f'mixed_nonnegative.{v}.{s}'}
                                   for s in ['a', 'b', 'c'])
        signed['residuals'].append(dict(label='mixed_nonnegative.' + str(v),
            terms=[[1, [v]], [-1, [a, a]], [-1, [b, b]], [-1, [c]], [-1, [c, c]]]))
        guards.append(dict(variable=v, auxiliary=[a, b, c]))
    certificate['guards'] = guards
    bridge = dict(schema='raw107_to_literal_mixed994_bridge_v1',
        retained_raw_indices=[identities[encoded(v)] for v in routes['variables']],
        mapped_994_guard_indices=sorted(mapped), raw107_guard_indices=sorted(seeds),
        replaced_raw_guard_indices=[644, 917],
        contracted_bound_replacements=[dict(contracted_variable=i,
            raw_variable=identities[encoded(v)]) for i, v in enumerate(routes['variables'])
            if identities[encoded(v)] in {644, 917}],
        statement='Raw integer projection and107 guards plus derived A/D signs supply a literal994 integer zero; conversely restore raw affine wires over Z and discard two guard triples.')
    raw_to_contracted = {identities[encoded(v)]: i for i, v in enumerate(routes['variables'])}
    positions = {v: j for j, v in enumerate(route_sign['guards'])}
    bridge['shared_guard_transfers'] = [dict(raw_variable=v, contracted_variable=raw_to_contracted[v],
        source_auxiliary=guards[j]['auxiliary'],
        target_auxiliary=list(range(667+3*positions[raw_to_contracted[v]],
                                    670+3*positions[raw_to_contracted[v]])))
        for j, v in enumerate(sorted(seeds))]
    bridge['new_994_guard_triples'] = [dict(raw_variable=v, contracted_variable=raw_to_contracted[v],
        target_auxiliary=list(range(667+3*positions[raw_to_contracted[v]],
                                    670+3*positions[raw_to_contracted[v]]))) for v in [644, 917]]
    # Literal parent metrics are collected before its hash enters projections.
    polynomial = {}
    for row in signed['residuals']:
        for j, (c, m) in enumerate(row['terms']):
            for d, n in row['terms'][:j+1]:
                key = tuple(sorted(m+n)); value = c*d*(1 if (d, n) == (c, m) else 2)
                # Distinct canonical terms make the diagonal test unambiguous.
                polynomial[key] = polynomial.get(key, 0) + value
    polynomial = {m: c for m, c in polynomial.items() if c}
    signed['metrics'] = dict(variables=len(signed['variables']), quadratic_rows=len(signed['residuals']),
        exact_degree=max(map(len, polynomial)), expanded_monomials=len(polynomial),
        max_abs_expanded_coefficient=max(map(abs, polynomial.values())))
    files = {'guarded.json': encoded(signed), 'domain_certificate.json': encoded(certificate),
             'arithmetic_interfaces.json': encoded(interface), 'BRIDGE994.json': encoded(bridge)}
    census = {}
    archive = REPO / pins['arithmetic_archive']
    need(digest(archive.read_bytes()) == pins['arithmetic_archive_sha256'], 'whole arithmetic engine archive')
    member = 'ConZFC_407_888_Quartics/code/integer_pipeline/terminal_elimination.py'
    with zipfile.ZipFile(archive) as z, tempfile.TemporaryDirectory(prefix='raw107-mixed-project-') as tmp:
        path = Path(tmp) / 'terminal_elimination.py'; data = z.read(member)
        need(digest(data) == pins['arithmetic_source_members'][member], 'literal generic signed optimizer')
        path.write_bytes(data)
        spec = importlib.util.spec_from_file_location('raw107_signed_optimizer', path)
        e = importlib.util.module_from_spec(spec); spec.loader.exec_module(e)
        for name, cap, affine in CONFIGS:
            child, cert, metrics = e.optimize(signed, max_support=cap, affine_support=affine)
            need(cert['unconstrained_removed'] == [], 'all raw mixed parent values uniquely restored')
            review = e.verify(signed, child, cert)
            for filename, value in [('equation.json', child), ('elimination_certificate.json', cert),
                                    ('expanded_polynomial.json', e.expand(child)),
                                    ('BUILD.json', dict(metrics=metrics, producer_internal_verification=review))]:
                files[name + '/' + filename] = encoded(value)
            census[name] = dict(metrics=child['metrics'], support_cap=cap, affine_cap=affine,
                                eliminated_coordinates=len(cert['steps']), unconstrained_removed=[])
    files['CENSUS.json'] = encoded(census)
    files['BUILD.json'] = encoded(dict(status='PASS', generator_sha256=digest(Path(__file__).read_bytes()),
        sha256={n: digest(b) for n, b in files.items()},
        scope='Complete raw mixed107-seed quartic and five signed projections; no natural pointwise restoration claim.'))
    return files, census


def main():
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('--check', action='store_true')
    args = parser.parse_args(); files, census = generate()
    for name, data in files.items():
        path = HERE / name
        if args.check:
            need(path.read_bytes() == data, 'deterministic entire artifact ' + name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(data)
    print(json.dumps(dict(status='PASS', check=args.check, metrics={n: {
        k: item['metrics'][k] for k in ['variables', 'quadratic_rows', 'expanded_monomials',
                                       'max_abs_expanded_coefficient']} for n, item in census.items()}), indent=2))


if __name__ == '__main__':
    main()
