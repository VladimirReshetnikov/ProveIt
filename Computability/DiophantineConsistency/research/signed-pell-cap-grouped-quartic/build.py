#!/usr/bin/env python3
"""Materialize one exact post-centered extension; execution on review HOLD."""
import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / 'research/signed-pell-cap-projections'
GROUPING = ROOT / 'research/signed-pell-cap-pool-grouping'
SEALS = {
    'research/signed-pell-cap-projections': '8d8fdd07fece21e07bd309a36c36c5f3602618de8e723378da1b1bcf78d9f06f',
    'research/signed-pell-cap-pool-grouping': '703bc45994f8816012f2436c5488e728bc91ef1b8505825e22c6a752bc1ba848',
}
GROUPS = [[2, 0, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15], [1]]
MAP_FILES = ['data/HORN_WITNESS_MAP.json', 'data/TRANSFORM.json',
             'data/terminal_elimination_certificate.json',
             'data/centered/translation_certificate.json',
             'data/plain/translation_certificate.json',
             'data/factorization_certificate.json', 'data/domain.json']


def need(ok, message):
    if not ok:
        raise ValueError(message)


def get(path):
    return json.loads(path.read_bytes())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def poly(terms):
    out = {}
    for coefficient, monomial in terms:
        key = tuple(sorted(monomial))
        out[key] = out.get(key, 0) + coefficient
    return {m: c for m, c in out.items() if c}


def terms(value):
    return [[c, list(m)] for m, c in sorted(value.items()) if c]


def add(*values):
    out = {}
    for value in values:
        for m, c in value.items():
            out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def scale(value, coefficient):
    return {m: coefficient * c for m, c in value.items() if coefficient * c}


def multiply(left, right):
    out = {}
    for m, c in left.items():
        for n, d in right.items():
            key = tuple(sorted(m + n))
            out[key] = out.get(key, 0) + c * d
    return {m: c for m, c in out.items() if c}


def sos(rows):
    return add(*(multiply(row, row) for row in rows))


def census(equation, polynomial):
    rows = [poly(row['terms']) for row in equation['residuals']]
    used = sorted({v for row in rows for m in row for v in m})
    return dict(declared_variables=len(equation['variables']), used_variables=used,
                unconstrained_variables=sorted(set(range(len(equation['variables']))) - set(used)),
                residuals=len(rows), residual_degree=max(map(len, (m for r in rows for m in r))),
                residual_height=max(abs(c) for r in rows for c in r.values()),
                largest_residual_support=max(map(len, rows)),
                degree=max(map(len, polynomial)), terms=len(polynomial),
                height=max(map(abs, polynomial.values())))


def authenticate():
    pins = get(HERE / 'SOURCE_PINS.json')
    for section, base in [('files', ROOT), ('core', HERE)]:
        for name, sha in pins[section].items():
            need(digest(base / name) == sha, 'whole pinned ' + section + ' ' + name)
    for name, sha in pins['closed_dependencies'].items():
        folder = ROOT / name
        manifest = folder / 'MANIFEST.json'
        need(digest(manifest) == sha, 'closed dependency seal ' + name)
        entries = get(manifest)['files']
        expected = {n: v['sha256'] if isinstance(v, dict) else v for n, v in entries.items()}
        actual = {str(p.relative_to(folder)): digest(p) for p in folder.rglob('*')
                  if p.is_file() and p != manifest}
        need(expected == actual, 'whole closed dependency ' + name)
        for n, value in entries.items():
            if isinstance(value, dict):
                need(value['bytes'] == (folder / n).stat().st_size, 'closed member length ' + n)
    need(all(pins['closed_dependencies'].get(n) == sha for n, sha in SEALS.items()),
         'exact accepted chart and grouping seals')


def produce():
    authenticate()
    parent = get(PARENT / 'data/centered/equation.json')
    old_polynomial = get(PARENT / 'data/centered/expanded_polynomial.json')
    report = get(GROUPING / 'STATIC.json')['charts']['centered']
    errors = [poly(value) for value in report['error_terms']]
    coupling = poly(report['coupling_terms'])
    old_rows = [poly(row['terms']) for row in parent['residuals']]
    need(len(parent['variables']) == 359 and len(old_rows) == 222, 'exact accepted chart layout')
    need(sos(old_rows) == poly(old_polynomial['terms']), 'whole accepted quartic')
    need(add(sos(errors), coupling) == old_rows[130], 'complete old pool')
    need(get(GROUPING / 'STATIC.json')['partitions']['five_groups'] == GROUPS, 'specified groups')
    groups = [sos([errors[i] for i in group]) for group in GROUPS]
    frame_items = sorted(old_rows[186].items())
    need(len(frame_items) == 47, 'all actual frame terms')
    frame_items = frame_items[1:] + frame_items[:1]
    left, right = dict(frame_items[:24]), dict(frame_items[24:])
    published = report['five_pool_two_frame_finite_layout_comparison']['best_in_this_finite_family']
    need(published['offset'] == 1 and published['cut'] == 24 and
         [terms(left), terms(right)] == published['frame_chunk_terms'], 'fixed frame split')
    definitions = [add({(359 + i,): 1}, scale(group, -1)) for i, group in enumerate(groups[:4])]
    definitions.append(add({(363,): 1}, scale(left, -1)))
    pool_consumer = add(*[{(i,): 1} for i in range(359, 363)], groups[4], coupling)
    frame_consumer = add({(363,): 1}, right)
    equation = copy.deepcopy(parent)
    equation.update(schema='signed_cap_grouped_quadratic_sos_v1',
                    parent_equation_schema=parent['schema'],
                    variant=parent['variant'] + ':post_centered_partial_sums',
                    parent_equation_sha256=digest(PARENT / 'data/centered/equation.json'),
                    parent_manifest_sha256=SEALS['research/signed-pell-cap-projections'],
                    grouping_manifest_sha256=SEALS['research/signed-pell-cap-pool-grouping'])
    equation['variables'] += [dict(kind='unrestricted_partial_sum', name='grouped_pool.partial' + str(i))
                              for i in range(4)]
    equation['variables'].append(dict(kind='unrestricted_partial_sum', name='grouped_frame.partial0'))
    equation['residuals'][130]['terms'] = terms(pool_consumer)
    equation['residuals'][186]['terms'] = terms(frame_consumer)
    equation['residuals'] += [dict(label='grouped_pool.definition' + str(i), terms=terms(value))
                              for i, value in enumerate(definitions[:4])]
    equation['residuals'].append(dict(label='grouped_frame.definition0', terms=terms(definitions[4])))
    values = groups[:4] + [left]
    extension = dict(schema='unique_post_chart_quadratic_extension_v1',
                     parent_equation_sha256=equation['parent_equation_sha256'],
                     old_coordinate_map=[[i, i] for i in range(359)],
                     old_row_map=[dict(old_row=i, consumer_row=i,
                                       subtract_definition_rows=list(range(222, 226)) if i == 130 else
                                       [226] if i == 186 else []) for i in range(222)],
                     new_coordinate_values=[dict(coordinate=359 + i, value=terms(value),
                                                 definition_row=222 + i,
                                                 consumer_row=130 if i < 4 else 186)
                                            for i, value in enumerate(values)],
                     groups=GROUPS, all16_error_terms=[terms(value) for value in errors],
                     coupling_terms=terms(coupling), frame_partition=[terms(left), terms(right)],
                     frame_rotation=1, frame_cut=24,
                     new_variable_occurrences={str(359 + i): [130 if i < 4 else 186, 222 + i]
                                               for i in range(5)},
                     all_old_coordinates_fixed=True, new_coordinates_unrestricted=True,
                     whole_polynomial_identity_claimed=False,
                     old_private_witnesses_and_free_coordinates_fixed=True,
                     optimizer_factorizer_projection_or_centering_executed=False)
    full = sos([poly(row['terms']) for row in equation['residuals']])
    polynomial = copy.deepcopy(old_polynomial)
    polynomial.update(variables=len(equation['variables']), terms=terms(full))
    inherited = {n: dict(sha256=digest(PARENT / n), complete_object=get(PARENT / n)) for n in MAP_FILES}
    binding = dict(schema='grouped_chart_parent_calibration_binding_v1',
                   parent_manifest_sha256=SEALS['research/signed-pell-cap-projections'],
                   grouping_manifest_sha256=SEALS['research/signed-pell-cap-pool-grouping'],
                   parent_equation_sha256=digest(PARENT / 'data/centered/equation.json'),
                   parent_polynomial_sha256=digest(PARENT / 'data/centered/expanded_polynomial.json'),
                   parent_calibration_binding_sha256=digest(PARENT / 'CALIBRATION_BINDING.json'),
                   inverse_order=['forget_five_new_coordinates', 'inverse_centered_translation',
                                  'inverse_initial_T_translation', 'restore_published_monic_steps',
                                  'accepted_Horn_private_witness_reconstruction'],
                   old_chart_identity_scope='Every old coordinate, including old private witnesses and old free-coordinate choices.',
                   inherited_Horn_scope_unchanged=True, new_source_semantics=False,
                   accepted_frontier_claim=False)
    result = {'equation.json': equation, 'expanded_polynomial.json': polynomial,
              'EXTENSION.json': extension, 'INHERITED_MAPS.json': inherited,
              'PARENT_BINDING.json': binding, 'METRICS.json': census(equation, full)}
    result['INDEX.json'] = dict(schema='grouped_chart_complete_data_index_v1',
                               files={n: dict(sha256=hashlib.sha256(encode(x)).hexdigest(),
                                              bytes=len(encode(x))) for n, x in result.items()})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--destination', type=Path, default=HERE / 'data')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    artifacts = produce()
    for name, value in artifacts.items():
        data = encode(value)
        target = args.destination / name
        if args.check:
            need(target.read_bytes() == data, 'whole deterministic artifact ' + name)
        else:
            need(not target.exists() or target.read_bytes() == data, 'refuse changed artifact ' + name)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    record = dict(status='PASS', optimized_python=bool(sys.flags.optimize), pure_check=args.check,
                  generated={n: hashlib.sha256(encode(value)).hexdigest() for n, value in artifacts.items()},
                  source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
                  optimizer_factorizer_projection_or_centering_executed=False,
                  prospective_metrics_replaced_by_actual_artifacts=True,
                  accepted_frontier_claim=False)
    data = encode(record)
    need(not args.output.exists() or args.output.read_bytes() == data, 'refuse changed receipt')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(data)
    print(data.decode(), end='')


if __name__ == '__main__':
    main()
