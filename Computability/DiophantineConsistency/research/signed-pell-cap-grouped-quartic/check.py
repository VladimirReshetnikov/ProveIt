#!/usr/bin/env python3
"""Independent whole-artifact post-chart audit; execution on review HOLD."""
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
NAMES = ['equation.json', 'expanded_polynomial.json', 'EXTENSION.json',
         'INHERITED_MAPS.json', 'PARENT_BINDING.json', 'METRICS.json', 'INDEX.json']


def need(ok, message):
    if not ok:
        raise ValueError(message)


def get(path):
    return json.loads(path.read_bytes())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def P(raw):
    out = {}
    for c, coordinates in raw:
        key = tuple(sorted(coordinates))
        out[key] = out.get(key, 0) + c
    return {m: c for m, c in out.items() if c}


def T(value):
    return [[c, list(m)] for m, c in sorted(value.items()) if c]


def V(i):
    return {(i,): 1}


def plus(*values):
    out = {}
    for value in values:
        for m, c in value.items():
            out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def times(left, right):
    out = {}
    for m, c in left.items():
        for n, d in right.items():
            key = tuple(sorted(m + n))
            out[key] = out.get(key, 0) + c * d
    return {m: c for m, c in out.items() if c}


def factor(value, coefficient):
    return {m: coefficient * c for m, c in value.items() if coefficient * c}


def collect_sos(rows):
    # Independent triangular collection: diagonal once, distinct pairs twice.
    result = {}
    for row in rows:
        items = sorted(row.items())
        for j, (m, c) in enumerate(items):
            for k in range(j, len(items)):
                n, d = items[k]
                key = tuple(sorted(m + n))
                result[key] = result.get(key, 0) + c * d * (1 if j == k else 2)
    return {m: c for m, c in result.items() if c}


def substitute(value, replacements):
    result = {}
    for m, c in value.items():
        term = {(): c}
        for coordinate in m:
            term = times(term, replacements.get(coordinate, V(coordinate)))
        result = plus(result, term)
    return result


def metrics(equation, full):
    rows = [P(r['terms']) for r in equation['residuals']]
    used = {i for row in rows for m in row for i in m}
    return dict(declared_variables=len(equation['variables']), used_variables=sorted(used),
                unconstrained_variables=[i for i in range(len(equation['variables'])) if i not in used],
                residuals=len(rows), residual_degree=max(len(m) for row in rows for m in row),
                residual_height=max(abs(c) for row in rows for c in row.values()),
                largest_residual_support=max(len(row) for row in rows),
                degree=max(len(m) for m in full), terms=len(full), height=max(abs(c) for c in full.values()))


def authenticate():
    pins = get(HERE / 'SOURCE_PINS.json')
    for section, base in [('files', ROOT), ('core', HERE)]:
        for name, sha in pins[section].items():
            need(digest(base / name) == sha, 'whole input/core ' + name)
    for name, sha in pins['closed_dependencies'].items():
        folder = ROOT / name
        manifest = folder / 'MANIFEST.json'
        need(digest(manifest) == sha, 'closed dependency seal ' + name)
        entries = get(manifest)['files']
        expected = {n: v['sha256'] if isinstance(v, dict) else v for n, v in entries.items()}
        need(expected == {str(p.relative_to(folder)): digest(p) for p in folder.rglob('*')
                          if p.is_file() and p != manifest}, 'complete closed inventory ' + name)
        for n, entry in entries.items():
            if isinstance(entry, dict):
                need((folder / n).stat().st_size == entry['bytes'], 'complete closed length ' + n)
    need(all(pins['closed_dependencies'].get(n) == sha for n, sha in SEALS.items()),
         'exact accepted centered chart and grouping theorem')
    if (HERE / 'MANIFEST.json').exists():
        need(get(HERE / 'MANIFEST.json')['files'] ==
             {str(p.relative_to(HERE)): digest(p) for p in HERE.rglob('*')
              if p.is_file() and p != HERE / 'MANIFEST.json'}, 'closed current packet')


def expected():
    parent = get(PARENT / 'data/centered/equation.json')
    old_full = get(PARENT / 'data/centered/expanded_polynomial.json')
    static = get(GROUPING / 'STATIC.json')['charts']['centered']
    old_rows = [P(r['terms']) for r in parent['residuals']]
    need(len(parent['variables']) == 359 and len(old_rows) == 222, 'exact old chart')
    # Explicit centered errors, independent of the materializer's STATIC reader.
    errors = [plus(V(169), factor(V(0), -1)),
              plus(V(174), *[factor(V(i), -2) for i in range(4)]),
              plus(V(181), factor(V(0), -1), factor(V(4), -1))]
    errors += [plus(V(y), factor(V(k), -1)) for y, k in
               [(188, 10), (194, 11), (198, 12), (202, 13), (206, 14), (210, 2),
                (214, 15), (218, 16), (222, 1), (226, 17), (230, 18), (234, 105), (239, 157)]]
    coupling = {(158, 247): -1}
    need([T(p) for p in errors] == static['error_terms'] and T(coupling) == static['coupling_terms'],
         'all literal centered errors and coupling')
    need(plus(collect_sos(errors), coupling) == old_rows[130], 'whole old pool')
    need(collect_sos(old_rows) == P(old_full['terms']), 'whole old polynomial')
    groups = [collect_sos([errors[i] for i in g]) for g in GROUPS]
    published = static['five_pool_two_frame_finite_layout_comparison']['best_in_this_finite_family']
    left, right = map(P, published['frame_chunk_terms'])
    keys = sorted(old_rows[186])
    need(len(keys) == 47 and set(left) == set(keys[1:25]) and
         set(right) == set(keys[25:] + keys[:1]), 'independent exact rotated frame partition')
    need(not (set(left) & set(right)) and plus(left, right) == old_rows[186], 'all old frame coefficients once')
    need(published['offset'] == 1 and published['cut'] == 24, 'fixed frame layout')
    values = groups[:4] + [left]
    definitions = [plus(V(359 + j), factor(value, -1)) for j, value in enumerate(values)]
    pool_consumer = plus(*[V(i) for i in range(359, 363)], groups[4], coupling)
    frame_consumer = plus(V(363), right)
    equation = copy.deepcopy(parent)
    equation['schema'] = 'signed_cap_grouped_quadratic_sos_v1'
    equation['parent_equation_schema'] = parent['schema']
    equation['variant'] = parent['variant'] + ':post_centered_partial_sums'
    equation['parent_equation_sha256'] = digest(PARENT / 'data/centered/equation.json')
    equation['parent_manifest_sha256'] = SEALS['research/signed-pell-cap-projections']
    equation['grouping_manifest_sha256'] = SEALS['research/signed-pell-cap-pool-grouping']
    equation['variables'] += [dict(kind='unrestricted_partial_sum', name='grouped_pool.partial' + str(i))
                              for i in range(4)] + [dict(kind='unrestricted_partial_sum', name='grouped_frame.partial0')]
    equation['residuals'][130]['terms'] = T(pool_consumer)
    equation['residuals'][186]['terms'] = T(frame_consumer)
    equation['residuals'] += [dict(label='grouped_pool.definition' + str(i), terms=T(definitions[i]))
                              for i in range(4)] + [dict(label='grouped_frame.definition0', terms=T(definitions[4]))]
    extension = dict(schema='unique_post_chart_quadratic_extension_v1',
                     parent_equation_sha256=equation['parent_equation_sha256'],
                     old_coordinate_map=[[i, i] for i in range(359)],
                     old_row_map=[dict(old_row=i, consumer_row=i,
                                       subtract_definition_rows=[222, 223, 224, 225] if i == 130 else
                                       [226] if i == 186 else []) for i in range(222)],
                     new_coordinate_values=[dict(coordinate=359 + i, value=T(value), definition_row=222 + i,
                                                 consumer_row=130 if i < 4 else 186)
                                            for i, value in enumerate(values)],
                     groups=GROUPS, all16_error_terms=[T(p) for p in errors], coupling_terms=T(coupling),
                     frame_partition=[T(left), T(right)], frame_rotation=1, frame_cut=24,
                     new_variable_occurrences={str(359 + i): [130 if i < 4 else 186, 222 + i]
                                               for i in range(5)},
                     all_old_coordinates_fixed=True, new_coordinates_unrestricted=True,
                     whole_polynomial_identity_claimed=False,
                     old_private_witnesses_and_free_coordinates_fixed=True,
                     optimizer_factorizer_projection_or_centering_executed=False)
    maps = {n: dict(sha256=digest(PARENT / n), complete_object=get(PARENT / n)) for n in MAP_FILES}
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
                   inherited_Horn_scope_unchanged=True, new_source_semantics=False, accepted_frontier_claim=False)
    return parent, old_full, equation, extension, maps, binding, published


def validate(artifacts):
    need(set(artifacts) == set(NAMES), 'entire seven-file data inventory')
    parent, old_full, want, extension, maps, binding, published = expected()
    equation = artifacts['equation.json']
    need(equation == want, 'whole equation: metadata, old/new variables, every row and coefficient')
    need(artifacts['EXTENSION.json'] == extension, 'whole coordinate/row/definition/privacy maps')
    need(artifacts['INHERITED_MAPS.json'] == maps, 'all seven complete inherited witness/inverse maps')
    need(artifacts['PARENT_BINDING.json'] == binding, 'whole parent and ordinary calibration binding')
    count = len(equation['variables'])
    rows = [P(row['terms']) for row in equation['residuals']]
    need(len({v['name'] for v in equation['variables']}) == count and
         equation['domain'] == 'unrestricted integers', 'unique names and unrestricted domain')
    for row, parsed in zip(equation['residuals'], rows):
        need(row['terms'] == T(parsed), 'canonical collected residual terms')
        need(all(type(c) is int and len(m) <= 2 and all(type(i) is int and 0 <= i < count for i in m)
                 for m, c in parsed.items()), 'all actual residuals integral and quadratic')
    replacements = {item['coordinate']: P(item['value']) for item in extension['new_coordinate_values']}
    need(all(len(m) <= 2 and all(i < 359 for i in m) for value in replacements.values() for m in value),
         'fresh coordinates have exact old-coordinate-only quadratic values')
    for i in range(359, count):
        hits = [j for j, row in enumerate(rows) if any(i in m for m in row)]
        need(hits == extension['new_variable_occurrences'][str(i)], 'complete new-variable privacy')
        need(all(m == (i,) for row in rows for m in row if i in m), 'new coordinates occur only linearly')
    old_rows = [P(row['terms']) for row in parent['residuals']]
    for item in extension['old_row_map']:
        reconstructed = plus(rows[item['consumer_row']],
                             *[factor(rows[j], -1) for j in item['subtract_definition_rows']])
        need(reconstructed == old_rows[item['old_row']], 'universal reconstruction of every old residual')
        need(substitute(rows[item['consumer_row']], replacements) == old_rows[item['old_row']],
             'universal completeness at every old assignment')
    need(all(substitute(rows[j], replacements) == {} for j in range(222, 227)),
         'all five definition residuals vanish under the unique extension')
    full = collect_sos(rows)
    header = copy.deepcopy(old_full)
    header.update(variables=count, terms=T(full))
    need(artifacts['expanded_polynomial.json'] == header, 'whole polynomial coefficients and complete header')
    need(substitute(full, replacements) == P(old_full['terms']), 'whole quartic under the unique extension')
    ds = rows[222:226]
    sum_ds = plus(*ds)
    cross = plus(*[factor(times(ds[i], ds[j]), -2) for i in range(4) for j in range(i + 1, 4)])
    difference = plus(factor(times(rows[130], sum_ds), 2), cross,
                      factor(times(rows[186], rows[226]), 2))
    need(plus(full, factor(P(old_full['terms']), -1)) == difference,
         'full universal SOS difference identity, not polynomial equality')
    actual_metrics = metrics(equation, full)
    need(artifacts['METRICS.json'] == actual_metrics and not actual_metrics['unconstrained_variables'],
         'complete actual census, no unconstrained coordinate')
    need(actual_metrics['degree'] == 4, 'actual quartic degree')
    need(dict(degree=actual_metrics['degree'], terms=actual_metrics['terms'], height=actual_metrics['height']) ==
         published['fixed_chart_quartic'] and count == published['fixed_chart_declared_variables'] and
         len(rows) == published['fixed_chart_residuals'], 'prospective calculation checked against complete actual artifact')
    coefficient_sha = hashlib.sha256((json.dumps(T(full), separators=(',', ':')) + '\n').encode()).hexdigest()
    need(coefficient_sha == published['whole_quartic_coefficients_sha256'], 'whole previously published coefficient vector')
    want_index = dict(schema='grouped_chart_complete_data_index_v1',
                      files={n: dict(sha256=hashlib.sha256(encode(x)).hexdigest(), bytes=len(encode(x)))
                             for n, x in artifacts.items() if n != 'INDEX.json'})
    need(artifacts['INDEX.json'] == want_index, 'complete data index and every whole artifact length/hash')
    return dict(metrics=actual_metrics, all_old_rows_reconstructed=True, all_old_coordinates_fixed=True,
                new_variable_privacy=extension['new_variable_occurrences'], complete_unique_extension=True,
                full_SOS_difference_identity=True, full_polynomial_under_extension=True,
                whole_coefficient_vector_sha256=coefficient_sha, all_seven_inherited_maps_whole=True,
                new_source_semantics=False, optimizer_factorizer_projection_or_centering_executed=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, default=HERE / 'data')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    authenticate()
    need({str(p.relative_to(args.packet)) for p in args.packet.rglob('*') if p.is_file()} == set(NAMES),
         'closed actual data file inventory')
    artifacts = {n: get(args.packet / n) for n in NAMES}
    need(all((args.packet / n).read_bytes() == encode(x) for n, x in artifacts.items()),
         'canonical whole JSON bytes')
    evidence = validate(artifacts)
    rejected = []

    def trial(label, mutate):
        changed = copy.deepcopy(artifacts)
        mutate(changed)
        try:
            validate(changed)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise ValueError('actual corruption accepted: ' + label)

    def change_row(artifact, index):
        artifact['equation.json']['residuals'][index]['terms'][0][0] += 1

    for i in [0, 129, 130, 186, 221, 222, 223, 224, 225, 226]:
        trial('actual residual coefficient ' + str(i), lambda a, i=i: change_row(a, i))
    trial('old coordinate metadata', lambda a: a['equation.json']['variables'][0].__setitem__('name', 'altered'))
    trial('fresh coordinate metadata', lambda a: a['equation.json']['variables'][359].__setitem__('kind', 'nonnegative'))
    trial('changed domain', lambda a: a['equation.json'].__setitem__('domain', 'natural numbers'))
    trial('old parent header', lambda a: a['equation.json'].__setitem__('parent_source_sha256', '0' * 64))
    trial('extra fresh occurrence', lambda a: a['equation.json']['residuals'][0]['terms'].append([1, [363]]))
    trial('new variable sign', lambda a: a['EXTENSION.json'].__setitem__('new_coordinates_unrestricted', False))
    trial('nonidentity old-coordinate map', lambda a: a['EXTENSION.json']['old_coordinate_map'][0].__setitem__(1, 1))
    trial('wrong reconstruction row', lambda a: a['EXTENSION.json']['old_row_map'][130]['subtract_definition_rows'].pop())
    trial('missing unique extension', lambda a: a['EXTENSION.json']['new_coordinate_values'].pop())
    trial('repeated error group', lambda a: a['EXTENSION.json']['groups'][0].append(1))
    trial('different frame rotation', lambda a: a['EXTENSION.json'].__setitem__('frame_rotation', 0))
    trial('false polynomial identity', lambda a: a['EXTENSION.json'].__setitem__('whole_polynomial_identity_claimed', True))
    trial('polynomial coefficient', lambda a: a['expanded_polynomial.json']['terms'][0].__setitem__(0, 0))
    trial('polynomial variable header', lambda a: a['expanded_polynomial.json'].__setitem__('variables', 359))
    trial('missing polynomial term', lambda a: a['expanded_polynomial.json']['terms'].pop())
    trial('inherited map body', lambda a: a['INHERITED_MAPS.json']['data/terminal_elimination_certificate.json']['complete_object']['steps'].pop())
    trial('inherited map hash', lambda a: a['INHERITED_MAPS.json']['data/HORN_WITNESS_MAP.json'].__setitem__('sha256', '0' * 64))
    trial('parent calibration', lambda a: a['PARENT_BINDING.json'].__setitem__('parent_calibration_binding_sha256', '0' * 64))
    trial('invented metric', lambda a: a['METRICS.json'].__setitem__('height', 0))
    trial('open generated inventory', lambda a: a['INDEX.json']['files'].pop('equation.json'))
    record = dict(status='PASS', optimized_python=bool(sys.flags.optimize),
                  checker_sha256=digest(Path(__file__)), source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
                  artifacts_sha256={n: digest(args.packet / n) for n in NAMES}, evidence=evidence,
                  rejected_actual_artifacts=rejected, producer_or_optimizer_executed=False,
                  scope='Exact post-centered unique extension, complete inherited maps and whole collected quartic only; no new source semantics.',
                  accepted_frontier_claim=False)
    data = encode(record)
    need(not args.output.exists() or args.output.read_bytes() == data, 'refuse changed receipt')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(data)
    print(json.dumps(dict(status='PASS', optimized_python=bool(sys.flags.optimize),
                          rejected_actual_artifacts=len(rejected)), sort_keys=True))


if __name__ == '__main__':
    main()
