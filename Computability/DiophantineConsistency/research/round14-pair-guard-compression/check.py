#!/usr/bin/env python3
"""Read-only literal audit of the ordinary Round14 pair-guard theorem."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def need(condition, label):
    if not condition:
        raise ValueError(label)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text())


def poly(terms):
    result = {}
    for coefficient, monomial in terms:
        key = tuple(sorted(monomial))
        result[key] = result.get(key, 0) + coefficient
    return {m: c for m, c in result.items() if c}


def combine(*items):
    return poly([[coefficient * scale, monomial]
                 for scale, terms in items for coefficient, monomial in terms])


def find(packet, label):
    matches = [(i, row) for i, row in enumerate(packet['residuals'])
               if row['label'] == label]
    need(len(matches) == 1, 'one actual row ' + label)
    return matches[0]


def pair_row(source, factored, pair):
    rs = pair['variables']
    need(len(rs) == 2 and len(set(rs)) == 2, 'distinct pair coordinates')
    rows = {}
    for kind, packet in [('mixed', source), ('factored', factored)]:
        i, row = find(packet, pair['row_label'])
        need(i == pair['row_indices'][kind], 'actual row index')
        rows[kind] = row['terms']
    need(rows['mixed'] == rows['factored'], 'same entire selected factored row')
    return rows['mixed']


def verify_variant(tag, cert, data):
    source, guarded, domain, factored, factor = data
    nv, nr = len(source['variables']), len(source['residuals'])
    expected = (550, 469, 63, 9) if tag == 'derived517' else (554, 476, 60, 8)
    need((nv, nr, len(domain['guard_indices']), len(cert['product_predicates'])) == expected,
         'exact original source shape and exchange count')
    need((cert['mixed_variables'], cert['mixed_rows']) == (nv, nr), 'mixed shape binding')
    need(guarded['variables'][:nv] == source['variables'], 'whole body metadata unchanged')
    need(guarded['residuals'][:nr] == source['residuals'], 'whole mixed body unchanged')
    need(len(guarded['residuals']) == nr + expected[2], 'all augmentation rows accounted')
    need(len(guarded['variables']) == nv + 3 * expected[2], 'all old triples accounted')
    old_aux = set(range(nv, len(guarded['variables'])))
    factor_body_rows = [i for i, r in enumerate(factored['residuals'])
                        if not r['label'].startswith('nonnegative.')]
    factor_body_coordinates = list(range(nv)) + list(range(len(guarded['variables']), len(factored['variables'])))
    need(cert['body_layout'] == dict(
        mixed=dict(coordinates=list(range(nv)), residual_indices=list(range(nr))),
        factored=dict(coordinates=factor_body_coordinates, residual_indices=factor_body_rows),
        old_guard_auxiliary_coordinates=sorted(old_aux)), 'complete noncontiguous body maps')
    need((len(factor_body_coordinates), len(factor_body_rows)) ==
         ((551, 468) if tag == 'derived517' else (555, 475)), 'exact factored body shape')
    for packet, indices, coordinates in [(source, range(nr), set(range(nv))),
                                          (factored, factor_body_rows, set(factor_body_coordinates))]:
        for i in indices:
            used = {v for _, monomial in packet['residuals'][i]['terms'] for v in monomial}
            need(used <= coordinates and not used & old_aux,
                 'old guard auxiliaries do not escape into any body row')
    retyped = ([118, 120, 122, 124, 126, 128, 130, 132, 134, 135, 148, 152]
               if tag == 'derived517' else
               [142, 144, 146, 148, 150, 152, 154, 156, 158, 159, 172, 176])
    for i, original in enumerate(guarded['variables']):
        expected_metadata = dict(original)
        if i in retyped:
            need(original['kind'] == 'square_difference', 'old private square type')
            expected_metadata['kind'] = 'gate'
        need(factored['variables'][i] == expected_metadata,
             'whole factor coordinate metadata with exact private retyping')
    need(digest(ROOT / (cert['source_directory'] + '/guarded.json')) == factor['input_sha256']
         and digest(ROOT / (cert['factored_directory'] + '/factored_source.json')) == factor['output_sha256'],
         'exact accepted factorization endpoints')
    need(cert['power_ports'] == domain['square_budget']['power_calls'], 'all actual power ports pinned')

    guards = domain['guard_indices']
    need(len(set(guards)) == len(guards), 'original guard list unique')
    need(all(type(v) is int and 0 <= v < nv for v in guards),
         'all guard targets belong to the body and avoid old auxiliaries')
    need(len(cert['guard_map']) == len(guards), 'complete guard map')
    need([r['label'] for r in factored['residuals'] if r['label'].startswith('nonnegative.')]
         == ['nonnegative.' + str(v) for v in guards], 'whole factored guard list')
    removed = {v for pair in cert['product_predicates'] for v in pair}
    need(len(removed) == 2 * expected[3], 'every exchanged pair disjoint')
    all_triples = [entry['auxiliary'] for entry in cert['guard_map']]
    flattened = [v for triple in all_triples for v in triple]
    need(len(flattened) == len(set(flattened)) and set(flattened) == old_aux,
         'old guard triples pairwise disjoint and exhaustive')
    for index, (variable, entry) in enumerate(zip(guards, cert['guard_map'])):
        aux = [nv + 3 * index + j for j in range(3)]
        label = 'nonnegative.' + str(variable)
        gi, grow = find(guarded, label)
        fi, frow = find(factored, label)
        terms = [[1, [variable]], [-1, [aux[0], aux[0]]],
                 [-1, [aux[1], aux[1]]], [-1, [aux[2]]], [-1, [aux[2], aux[2]]]]
        need(poly(grow['terms']) == poly(terms) and frow == grow, 'whole Legendre graph')
        need(entry == dict(original_index=index, raw_variable=variable,
                           name=source['variables'][variable]['name'], guarded_row=gi,
                           factored_row=fi, auxiliary=aux,
                           action='replace_by_pair_product' if variable in removed else 'retain'),
             'complete exact guard row/name/auxiliary map')
    for kind, packet in [('guarded', guarded), ('factored', factored)]:
        occurrences = {v: set() for v in old_aux}
        for i, row in enumerate(packet['residuals']):
            for v in {v for _, monomial in row['terms'] for v in monomial} & old_aux:
                occurrences[v].add(i)
        for entry in cert['guard_map']:
            for v in entry['auxiliary']:
                need(occurrences[v] == {entry[kind + '_row']},
                     'each old auxiliary occurs only in its own guard graph in both views')
    retained = [v for v in guards if v not in removed]
    need(cert['retained_scalar_variables'] == retained, 'all untouched scalar predicates retained')
    need(set(removed) <= set(guards), 'all exchanged coordinates really guarded')
    need(cert['old_scalar_predicates'] == len(guards)
         and cert['replacement_scalar_predicates'] == len(retained)
         and cert['replacement_product_predicates'] == expected[3], 'predicate counts only')

    range_names = ['a', 'b', 'c', 'd', 'S', 'Sp', 'u', 'vq', 'index', 'derived_label_sum']
    layouts = [(0, [1, 2, 3, 9] if tag == 'derived517' else [1, 2, 3]),
               (4, [5]), (6, [7]), ('choose0', ['choose1', 8])]
    expected_denominators = [200, 222, 234, 185] if tag == 'derived517' else [218, 240, 252, 203]
    need(len(cert['groups']) == 4, 'four actual anchor groups')
    products, identities = [], 0
    for group, (anchor_name, target_names), denominator in zip(cert['groups'], layouts, expected_denominators):
        need(group['common_numerator'] == denominator, 'literal common numerator port')
        pairs = [group['anchor']] + group['targets']
        need(len(pairs) == len(target_names) + 1, 'complete group membership')
        anchor_terms = None
        for pair, name in zip(pairs, [anchor_name] + target_names):
            stem = name if isinstance(name, str) else 'range' + str(name)
            suffix = '.rslack' if isinstance(name, str) else '.slack'
            expected_names = [stem + '.remainder', stem + suffix]
            expected_label = stem + '.remainder_bound' if isinstance(name, str) else 'crt.range.' + range_names[name] + '.remainder_bound'
            need(pair['name'] == stem and pair['row_label'] == expected_label, 'complete actual pair labels')
            need([source['variables'][v]['name'] for v in pair['variables']] == expected_names,
                 'complete actual pair coordinate names')
            terms = pair_row(source, factored, pair)
            r, s = pair['variables']
            need(poly(terms) == poly([[-1, []], [1, [denominator]], [-1, [r]], [-1, [s]]]),
                 'entire common-numerator residual')
            if anchor_terms is None:
                anchor_terms = terms
                a, b = pair['variables']
                need(a in retained and b in retained, 'anchor pair individually retained')
            else:
                need(combine((1, anchor_terms), (-1, terms)) == poly([[1, [r]], [1, [s]], [-1, [a]], [-1, [b]]]),
                     'full sparse row-difference identity')
                products.append([r, s]); identities += 1

    digit = cert['digit_exchange']
    anchor, target, fact = digit['anchor'], digit['target'], digit['factorial_anchor']
    D, a = anchor['variables']; B, s = target['variables']; Df, u, v = fact['variables']
    need(D == Df and (D, u, v, a, B, s) == ((6, 8, 9, 189, 28, 196) if tag == 'derived517' else (46, 48, 49, 207, 52, 214)),
         'exact factorial/digit ports')
    need([source['variables'][j]['name'] for j in (D, u, v, a, B, s)]
         == ['choose0.output', 'fact0.remainder', 'fact0.slack', 'choose0.oslack', 'choose1.output', 'choose1.oslack'],
         'exact factorial/digit names')
    need(anchor['row_label'] == 'choose0.digit_bound' and target['row_label'] == 'choose1.digit_bound'
         and fact['row_label'] == 'fact0.remainder_bound', 'exact digit/factorial cuts')
    first, second = pair_row(source, factored, anchor), pair_row(source, factored, target)
    Q = 183 if tag == 'derived517' else 201
    need(poly(first) == poly([[-1, []], [1, [Q]], [-1, [D]], [-1, [a]]])
         and poly(second) == poly([[-1, []], [1, [Q]], [-1, [B]], [-1, [s]]]), 'entire digit residuals')
    need(combine((1, first), (-1, second)) == poly([[1, [B]], [1, [s]], [-1, [D]], [-1, [a]]]),
         'exact digit shared-sum identity')
    for kind, packet in [('mixed', source), ('factored', factored)]:
        i, row = find(packet, fact['row_label'])
        need(i == fact['row_indices'][kind] and poly(row['terms']) == poly([[-1, []], [1, [D]], [-1, [u]], [-1, [v]]]),
             'early D-positive factorial identity')
    need(all(j in retained for j in (u, v, a)), 'early digit anchors individually retained')
    need(D not in guards, 'D positivity is derived rather than silently guarded')
    products.append([B, s]); identities += 2
    need(products == cert['product_predicates'], 'all and only the separately guarded products')
    return dict(original_scalar_predicates=len(guards), retained_scalar_predicates=len(retained),
                separate_product_predicates=len(products), exact_pair_identities=identities,
                mixed_variables=nv, mixed_rows=nr, all_original_Legendre_graphs_checked=True,
                factored_body_coordinates=len(factor_body_coordinates), factored_body_rows=len(factor_body_rows),
                old_auxiliaries_only_in_their_own_guards=True,
                selected_factored_rows_identical=True, power_ports=len(cert['power_ports']))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pins = load(HERE / 'SOURCE_PINS.json')
    for name, h in pins['files'].items():
        need(digest(ROOT / name) == h, 'whole immutable parent ' + name)
    for name, h in pins['own_files'].items():
        need(digest(HERE / name) == h, 'whole author core ' + name)
    if (HERE / 'MANIFEST.json').exists():
        entries = load(HERE / 'MANIFEST.json')['files']
        need(set(entries) == {str(p.relative_to(HERE)) for p in HERE.rglob('*')
                             if p.is_file() and p != HERE / 'MANIFEST.json'}, 'closed own inventory')
        for name, h in entries.items():
            need(digest(HERE / name) == h, 'whole sealed member ' + name)
    certificate = load(HERE / 'CERTIFICATE.json')
    need(certificate['schema'] == 'pointwise_integer_pair_guard_exchange_v1'
         and certificate['body_coordinates_fixed'] is True
         and certificate['equations_materialized'] is False
         and certificate['projected_metrics_claimed'] is False, 'ordinary-only scope')
    need(set(certificate['variants']) == {'derived517', 'hybrid519'}, 'both complete ancestries')
    results, data_sets, rejects = {}, {}, []
    for tag, cert in certificate['variants'].items():
        base, factor = ROOT / cert['source_directory'], ROOT / cert['factored_directory']
        data = [load(base / name) for name in ['mixed_source.json', 'guarded.json', 'domain_certificate.json']]
        data += [load(factor / name) for name in ['factored_source.json', 'factorization_certificate.json']]
        data_sets[tag] = data
        results[tag] = verify_variant(tag, cert, data)
        def reject(label, mutate):
            badcert, bad = deepcopy(cert), deepcopy(data)
            mutate(badcert, bad)
            try:
                verify_variant(tag, badcert, bad)
            except (ValueError, KeyError, IndexError):
                rejects.append(tag + ':' + label)
            else:
                raise ValueError('accepted actual corruption ' + label)
        reject('wrong shared numerator', lambda c, d: c['groups'][0].__setitem__('common_numerator', 0))
        reject('anchor removed', lambda c, d: c['retained_scalar_variables'].remove(c['groups'][0]['anchor']['variables'][0]))
        reject('one product omitted', lambda c, d: c['product_predicates'].pop())
        reject('cross-group pair', lambda c, d: c['groups'][1]['targets'][0].__setitem__('variables', c['groups'][0]['targets'][0]['variables']))
        reject('guard auxiliary drift', lambda c, d: c['guard_map'][0]['auxiliary'].__setitem__(0, 0))
        reject('actual guard sign', lambda c, d: d[1]['residuals'][c['guard_map'][0]['guarded_row']]['terms'][1].__setitem__(0, 1))
        reject('actual mixed pair constant', lambda c, d: d[0]['residuals'][c['groups'][0]['targets'][0]['row_indices']['mixed']]['terms'][0].__setitem__(0, -2))
        reject('actual factored pair constant', lambda c, d: d[3]['residuals'][c['groups'][0]['targets'][0]['row_indices']['factored']]['terms'][0].__setitem__(0, -2))
        reject('early factorial constant', lambda c, d: d[0]['residuals'][c['digit_exchange']['factorial_anchor']['row_indices']['mixed']]['terms'][0].__setitem__(0, 0))
        reject('digit product wrong coordinate', lambda c, d: c['product_predicates'][-1].__setitem__(0, c['digit_exchange']['anchor']['variables'][0]))
        reject('power interface drift', lambda c, d: c['power_ports'][0]['output'][0][1].__setitem__(0, 0))
        reject('unlisted original guard', lambda c, d: d[2]['guard_indices'].pop())
        reject('escaping factored guard auxiliary', lambda c, d: d[3]['residuals'][c['body_layout']['factored']['residual_indices'][-1]]['terms'].append([1, [c['body_layout']['old_guard_auxiliary_coordinates'][0]]]))
        reject('missing appended factored body coordinate', lambda c, d: c['body_layout']['factored']['coordinates'].pop())

    controls = 0
    for r in range(-80, 81):
        for s in range(-80, 81):
            if r + s >= 0:
                need((r >= 0 and s >= 0) == (r * s >= 0), 'integer-pair diagnostic')
                controls += 1
    need((-1) * (-1) >= 0 and -1 + -1 < 0, 'missing anchor counterexample')
    need((-1 * 2) ** 2 > 0 and -1 < 0, 'combined-product counterexample')
    for a in range(-20, 21):
        for b in range(-20, 21):
            for c in range(-20, 21):
                need(a * a + b * b + c * (c + 1) >= 0, 'integer Legendre-graph diagnostic')
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), variants=results,
                  integer_pair_controls=controls, Legendre_nonnegative_controls=41 ** 3,
                  rejected_actual_artifact_corruptions=rejects,
                  source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
                  certificate_sha256=digest(HERE / 'CERTIFICATE.json'),
                  incoming_or_parent_or_optimizer_or_lean_executed=False,
                  source_equations_modified=False, projected_metrics_claimed=False,
                  scope='Finite literal premises for the unbounded fixed-tuple guard equivalence in PROOF.md.')
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output.exists():
        need(args.output.read_text() == text, 'refuse changed receipt overwrite')
    else:
        args.output.write_text(text)
    print(json.dumps(dict(status='PASS', variants=2, exact_pair_identities=sum(v['exact_pair_identities'] for v in results.values()),
                          rejected_actual_artifact_corruptions=len(rejects), optimized_python=bool(sys.flags.optimize)), sort_keys=True))


if __name__ == '__main__':
    main()
