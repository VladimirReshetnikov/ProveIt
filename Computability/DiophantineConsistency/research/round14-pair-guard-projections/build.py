#!/usr/bin/env python3
"""Literal Round14 pair-guard adapter with independently reviewed full engine closure."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ORDINARY = ROOT / 'research/round14-pair-guard-compression'
CONFIGS = {
    'support8': dict(max_support=8, affine_support=None, quadratic_first=False),
    'support16': dict(max_support=16, affine_support=None, quadratic_first=False),
    'support32': dict(max_support=32, affine_support=None, quadratic_first=False),
    'support16_affine3': dict(max_support=16, affine_support=3, quadratic_first=False),
    'support16_affine4': dict(max_support=16, affine_support=4, quadratic_first=False),
    'support16_quadratic_first': dict(max_support=16, affine_support=None, quadratic_first=True),
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(obj):
    return (json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n').encode()


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text())


def inputs():
    pins = load(HERE / 'SOURCE_PINS.json')
    for name, h in pins['parent_files'].items():
        need(digest(ROOT / name) == h, 'immutable parent ' + name)
    for name, h in pins['own_core'].items():
        need(digest(HERE / name) == h, 'reviewed author core ' + name)
    manifest = load(ORDINARY / 'MANIFEST.json')
    need(digest(ORDINARY / 'MANIFEST.json') == pins['ordinary_manifest_sha256'], 'ordinary seal')
    need(set(manifest['files']) == {str(p.relative_to(ORDINARY)) for p in ORDINARY.rglob('*')
                                  if p.is_file() and p != ORDINARY / 'MANIFEST.json'}, 'closed ordinary packet')
    for name, h in manifest['files'].items():
        need(digest(ORDINARY / name) == h, 'ordinary member ' + name)
    need(digest(HERE / 'vendor/terminal_elimination.py') == pins['engine_sha256'], 'reviewed engine bytes')
    return pins, load(ORDINARY / 'CERTIFICATE.json')


def remap(terms, mapping):
    return [[c, sorted(mapping[v] for v in m)] for c, m in terms]


def make_source(tag, cert):
    parent_path = ROOT / cert['factored_directory'] / 'factored_source.json'
    parent = load(parent_path)
    layout = cert['body_layout']['factored']
    coordinates, rows = layout['coordinates'], layout['residual_indices']
    mapping = {old: new for new, old in enumerate(coordinates)}
    row_map = {old: new for new, old in enumerate(rows)}
    variables = [deepcopy(parent['variables'][v]) for v in coordinates]
    residuals = [dict(label=parent['residuals'][i]['label'],
                      terms=remap(parent['residuals'][i]['terms'], mapping)) for i in rows]
    predicates = []
    for entry in cert['guard_map']:
        if entry['action'] == 'retain':
            old = entry['raw_variable']
            predicates.append(dict(kind='scalar', old_variables=[old], variables=[mapping[old]],
                                   original_guard_indices=[entry['original_index']], label='scalar.' + str(old)))
    for a, b in cert['product_predicates']:
        old_indices = [e['original_index'] for e in cert['guard_map'] if e['raw_variable'] in (a, b)]
        predicates.append(dict(kind='product', old_variables=[a, b], variables=[mapping[a], mapping[b]],
                               original_guard_indices=old_indices, label='product.' + str(a) + '.' + str(b)))
    for index, predicate in enumerate(predicates):
        aux = list(range(len(variables), len(variables) + 3))
        for v, suffix in zip(aux, ['a', 'b', 'c']):
            variables.append(dict(kind='integer_guard', name='pairguard.' + predicate['label'] + '.' + suffix))
        target = [1, predicate['variables']]
        terms = [target, [-1, [aux[0], aux[0]]], [-1, [aux[1], aux[1]]],
                 [-1, [aux[2]]], [-1, [aux[2], aux[2]]]]
        predicate.update(index=index, auxiliary=aux, row=len(residuals))
        residuals.append(dict(label='pairguard.' + predicate['label'], terms=terms))
    equation = {k: deepcopy(v) for k, v in parent.items() if k not in ['variables', 'residuals']}
    equation.update(variables=variables, residuals=residuals,
                    variant=parent['variant'] + ':individual_pair_guards',
                    ordinary_guard_exchange_manifest_sha256=digest(ORDINARY / 'MANIFEST.json'))
    contract = dict(schema='pointwise_body_guard_map_v1', ancestry=tag,
                    factored_parent_sha256=digest(parent_path),
                    ordinary_manifest_sha256=digest(ORDINARY / 'MANIFEST.json'),
                    body_variable_map=[[old, mapping[old]] for old in coordinates],
                    body_row_map=[[old, row_map[old]] for old in rows],
                    excluded_old_guard_auxiliaries=cert['body_layout']['old_guard_auxiliary_coordinates'],
                    predicates=predicates,
                    old_guard_witnesses='Fresh existential Legendre choices on reverse; not polynomial restorations.',
                    new_guard_witnesses='Fresh existential Legendre choices on forward; body fixed.',
                    whole_guarded_tuple_bijection_claimed=False,
                    forward='Discard old guard triples; copy every body coordinate through body_variable_map; choose each new triple.',
                    reverse='Invert the complete body map; ordinary pair theorem restores every old sign; choose every old triple.')
    used = {v for row in residuals for _, m in row['terms'] for v in m}
    contract['unused_body_coordinates'] = [[old, mapping[old]] for old in coordinates if mapping[old] not in used]
    ports = [{key: remap(value, mapping) for key, value in power.items()} for power in cert['power_ports']]
    identities = []
    def add(kind, cuts, target):
        identities.append(dict(kind=kind, old_cuts=cuts,
                               new_cuts=[[scale, row_map[row]] for scale, row in cuts],
                               target=remap(target, mapping)))
    for group in cert['groups']:
        anchor = group['anchor'];a, b = anchor['variables']
        for pair in group['targets']:
            r, s = pair['variables']
            add('pair_sum', [[1, anchor['row_indices']['factored']], [-1, pair['row_indices']['factored']]],
                [[1, [r]], [1, [s]], [-1, [a]], [-1, [b]]])
    d = cert['digit_exchange'];D, a = d['anchor']['variables'];B, s = d['target']['variables']
    add('digit_sum', [[1, d['anchor']['row_indices']['factored']], [-1, d['target']['row_indices']['factored']]],
        [[1, [B]], [1, [s]], [-1, [D]], [-1, [a]]])
    D, u, v = d['factorial_anchor']['variables']
    add('early_D_positive', [[1, d['factorial_anchor']['row_indices']['factored']]],
        [[-1, []], [1, [D]], [-1, [u]], [-1, [v]]])
    bindings = dict(schema='complete_pair_guard_ideal_bindings_v1', identities=identities,
                    original_power_ports=cert['power_ports'], remapped_power_ports=ports,
                    power_port_meanings_unchanged=True)
    return equation, contract, bindings


def census(equation, polynomial):
    return dict(variables=len(equation['variables']), rows=len(equation['residuals']),
                degree=max((len(m) for _, m in polynomial['terms']), default=0),
                monomials=len(polynomial['terms']), height=max((abs(c) for c, _ in polynomial['terms']), default=0),
                row_height=max((abs(c) for r in equation['residuals'] for c, _ in r['terms']), default=0))


def materialize(directory, mode):
    pins, certificate = inputs()
    need(not directory.exists() or not any(directory.iterdir()), 'output must be absent or empty')
    directory.mkdir(parents=True, exist_ok=True)
    def put(name, value):
        path = directory / name;path.parent.mkdir(parents=True, exist_ok=True);path.write_bytes(canonical(value))
    engine = None
    if mode == 'full':
        # Root and reduce_ten reviewed the complete closure before authorizing this branch.
        spec = importlib.util.spec_from_file_location('reviewed_round14_integer_engine', HERE / 'vendor/terminal_elimination.py')
        engine = importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
    summaries = {}
    for tag, cert in certificate['variants'].items():
        source, contract, bindings = make_source(tag, cert)
        prefix = 'sources/' + tag + '/'
        for name, obj in [('equation.json', source), ('BODY_GUARD_MAP.json', contract), ('IDEAL_BINDINGS.json', bindings)]:
            put(prefix + name, obj)
        summaries[tag] = dict(source_variables=len(source['variables']), source_rows=len(source['residuals']), profiles={})
        if engine is None:
            continue
        raw_poly = engine.expand(source);put(prefix + 'expanded_polynomial.json', raw_poly)
        put(prefix + 'METRICS.json', census(source, raw_poly))
        for config, options in CONFIGS.items():
            projected, projection, report = engine.optimize(source, **options)
            verification = engine.verify(source, projected, projection)
            poly = engine.expand(projected)
            out = 'profiles/' + tag + '/' + config + '/'
            for name, obj in [('equation.json', projected), ('terminal_elimination_certificate.json', projection),
                              ('expanded_polynomial.json', poly), ('METRICS.json', census(projected, poly)),
                              ('ENGINE_VERIFICATION.json', report | verification)]:
                put(out + name, obj)
            shifts = {i: -1 for i, v in enumerate(projected['variables'])
                      if v['name'].startswith('crt.encoded') or v['name'] in ('t0', 'M0') or v['name'].endswith('minus1')}
            centered = deepcopy(projected);centered.pop('metrics', None);centered.pop('elimination', None)
            for row in centered['residuals']:
                polynomial = engine.normalize(row['terms'])
                for variable, shift in shifts.items():
                    polynomial = engine.substitute(polynomial, variable, {(variable,): 1, (): shift})
                row['terms'] = engine.as_terms(polynomial)
            centered['variant'] += ':integral_translation'
            translation = dict(schema='integral_translation_v1', input_sha256=sha256(canonical(projected)).hexdigest(),
                               output_sha256=sha256(canonical(centered)).hexdigest(),
                               shifts=[[i, s] for i, s in sorted(shifts.items())],
                               convention='old_coordinate = new_coordinate + shift', inverse='new_coordinate = old_coordinate - shift')
            centered_poly = engine.expand(centered)
            for name, obj in [('equation.json', centered), ('translation_certificate.json', translation),
                              ('expanded_polynomial.json', centered_poly), ('METRICS.json', census(centered, centered_poly))]:
                put(out + 'centered/' + name, obj)
            summaries[tag]['profiles'][config] = dict(plain=census(projected, poly), centered=census(centered, centered_poly))
    index = dict(schema='round14_pair_guard_release_v1', mode=mode,
                 ordinary_manifest_sha256=pins['ordinary_manifest_sha256'], configurations=CONFIGS,
                 reviewed_engine_executed=mode == 'full', incoming_or_lean_executed=False,
                 summaries=summaries, canonical_or_common_files_modified=False,
                 accepted_or_promoted_metrics_claimed=False,
                 files={str(p.relative_to(directory)):digest(p) for p in sorted(directory.rglob('*')) if p.is_file()})
    put('INDEX.json', index)
    return index


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=['source-only', 'full'], default='source-only')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        with tempfile.TemporaryDirectory(prefix='round14-pair-guard-build-') as temp:
            result = materialize(Path(temp) / 'data', args.mode)
            generated = Path(temp) / 'data'
            expected = {str(p.relative_to(generated)) for p in generated.rglob('*') if p.is_file()}
            need(expected == {str(p.relative_to(args.output)) for p in args.output.rglob('*') if p.is_file()}, 'closed deterministic output inventory')
            for name in expected:
                need((generated / name).read_bytes() == (args.output / name).read_bytes(), 'deterministic member ' + name)
    else:
        result = materialize(args.output, args.mode)
    print(json.dumps(dict(status='PASS', mode=args.mode, deterministic_check=args.check,
                          source_summaries=result['summaries'], engine_executed=args.mode == 'full'), sort_keys=True))


if __name__ == '__main__':
    main()
