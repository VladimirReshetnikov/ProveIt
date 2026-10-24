#!/usr/bin/env python3
"""Independent sparse collector; imports no producer, optimizer, parent or incoming code."""
import argparse
from collections import Counter, defaultdict
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

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


def need(condition, label):
    if not condition:
        raise ValueError(label)


def canonical(obj):
    return (json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n').encode()


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text())


def poly(terms):
    result = defaultdict(int)
    for c, m in terms:
        need(type(c) is int and all(type(v) is int and v >= 0 for v in m), 'integer sparse terms')
        result[tuple(sorted(m))] += c
    return {m: c for m, c in result.items() if c}


def terms(p):
    return [[c, list(m)] for m, c in sorted(p.items())]


def mul(a, b):
    result = defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            result[tuple(sorted(ma + mb))] += ca * cb
    return {m: c for m, c in result.items() if c}


def replace(p, v, value):
    result = defaultdict(int)
    for monomial, coefficient in p.items():
        q = {(): coefficient}
        for x in monomial:
            q = mul(q, value if x == v else {(x,): 1})
        for m, c in q.items():
            result[m] += c
    return {m: c for m, c in result.items() if c}


def degree(p):
    return max((len(m) for m in p), default=0)


def expansion(equation):
    result = defaultdict(int)
    for row in equation['residuals']:
        p = poly(row['terms'])
        need(degree(p) <= 2, 'quadratic residual')
        for m, c in mul(p, p).items():
            result[m] += c
    return {m: c for m, c in result.items() if c}


def metrics(equation, expanded):
    return dict(variables=len(equation['variables']), rows=len(equation['residuals']),
                degree=degree(expanded), monomials=len(expanded),
                height=max((abs(c) for c in expanded.values()), default=0),
                row_height=max((abs(c) for r in equation['residuals'] for c, _ in r['terms']), default=0))


def remap(ts, mapping):
    return [[c, sorted(mapping[v] for v in m)] for c, m in ts]


def source_check(tag, cert, source, contract, bindings):
    parent = load(ROOT / cert['factored_directory'] / 'factored_source.json')
    layout = cert['body_layout']['factored'];body = layout['coordinates'];rows = layout['residual_indices']
    vm = {old: i for i, old in enumerate(body)};rm = {old: i for i, old in enumerate(rows)}
    nb, nr = len(body), len(rows)
    need(contract['body_variable_map'] == [[v, vm[v]] for v in body]
         and contract['body_row_map'] == [[i, rm[i]] for i in rows], 'entire noncontiguous body maps')
    need(contract['excluded_old_guard_auxiliaries'] == cert['body_layout']['old_guard_auxiliary_coordinates'], 'all old auxiliaries excluded')
    need(contract['factored_parent_sha256'] == digest(ROOT / cert['factored_directory'] / 'factored_source.json')
         and contract['ordinary_manifest_sha256'] == digest(ORDINARY / 'MANIFEST.json'), 'exact calibrated ancestry')
    need(contract['schema'] == 'pointwise_body_guard_map_v1' and contract['ancestry'] == tag
         and contract['whole_guarded_tuple_bijection_claimed'] is False, 'body-only existential correspondence')
    need(source['variables'][:nb] == [parent['variables'][v] for v in body], 'whole factored body metadata')
    expected_rows = [dict(label=parent['residuals'][i]['label'], terms=remap(parent['residuals'][i]['terms'], vm)) for i in rows]
    need(source['residuals'][:nr] == expected_rows, 'every complete factored body row unchanged through map')
    old_meta = {k: deepcopy(v) for k, v in parent.items() if k not in ['variables', 'residuals']}
    old_meta.update(variant=parent['variant'] + ':individual_pair_guards',
                    ordinary_guard_exchange_manifest_sha256=digest(ORDINARY / 'MANIFEST.json'))
    need({k: v for k, v in source.items() if k not in ['variables', 'residuals']} == old_meta, 'whole source signature/domain')
    expected_predicates = []
    for e in cert['guard_map']:
        if e['action'] == 'retain':
            v = e['raw_variable'];expected_predicates.append(dict(kind='scalar', old_variables=[v], variables=[vm[v]],
                original_guard_indices=[e['original_index']], label='scalar.' + str(v)))
    for a, b in cert['product_predicates']:
        expected_predicates.append(dict(kind='product', old_variables=[a, b], variables=[vm[a], vm[b]],
            original_guard_indices=[e['original_index'] for e in cert['guard_map'] if e['raw_variable'] in (a, b)],
            label='product.' + str(a) + '.' + str(b)))
    for i, predicate in enumerate(expected_predicates):
        aux = [nb + 3 * i + j for j in range(3)]
        predicate.update(index=i, auxiliary=aux, row=nr + i)
        expected_variables = [dict(kind='integer_guard', name='pairguard.' + predicate['label'] + '.' + suffix)
                              for suffix in ['a', 'b', 'c']]
        need(source['variables'][aux[0]:aux[2] + 1] == expected_variables, 'fresh individual guard triple')
        graph = [[1, predicate['variables']], [-1, [aux[0], aux[0]]], [-1, [aux[1], aux[1]]],
                 [-1, [aux[2]]], [-1, [aux[2], aux[2]]]]
        need(source['residuals'][nr + i] == dict(label='pairguard.' + predicate['label'], terms=graph),
             'exact independent scalar/product Legendre graph')
    need(contract['predicates'] == expected_predicates, 'complete old/new scalar and separate-product predicate map')
    need(len(source['variables']) == nb + 3 * len(expected_predicates)
         and len(source['residuals']) == nr + len(expected_predicates), 'all coordinates and rows accounted')
    used = {v for row in source['residuals'] for _, m in row['terms'] for v in m}
    unused = [[v, vm[v]] for v in body if vm[v] not in used]
    need(contract['unused_body_coordinates'] == unused
         and unused == ([[136, 136], [138, 138]] if tag == 'derived517' else [[160, 160], [162, 162]]),
         'both genuinely unconstrained body coordinates declared, not silently omitted')
    ports = [{k: remap(value, vm) for k, value in call.items()} for call in cert['power_ports']]
    need(bindings['original_power_ports'] == cert['power_ports'] and bindings['remapped_power_ports'] == ports
         and bindings['power_port_meanings_unchanged'] is True, 'all19 unchanged source power interfaces')
    identities = []
    def identity(kind, cuts, target):
        newcuts = [[scale, rm[row]] for scale, row in cuts]
        entry = dict(kind=kind, old_cuts=cuts, new_cuts=newcuts, target=remap(target, vm))
        acc = defaultdict(int)
        for scale, row in newcuts:
            for m, c in poly(source['residuals'][row]['terms']).items():
                acc[m] += scale * c
        need({m: c for m, c in acc.items() if c} == poly(entry['target']), 'complete actual source ideal identity')
        identities.append(entry)
    for group in cert['groups']:
        a, b = group['anchor']['variables']
        for pair in group['targets']:
            r, s = pair['variables']
            identity('pair_sum', [[1, group['anchor']['row_indices']['factored']], [-1, pair['row_indices']['factored']]],
                     [[1, [r]], [1, [s]], [-1, [a]], [-1, [b]]])
    d = cert['digit_exchange'];D, a = d['anchor']['variables'];B, s = d['target']['variables']
    identity('digit_sum', [[1, d['anchor']['row_indices']['factored']], [-1, d['target']['row_indices']['factored']]],
             [[1, [B]], [1, [s]], [-1, [D]], [-1, [a]]])
    D, u, v = d['factorial_anchor']['variables']
    identity('early_D_positive', [[1, d['factorial_anchor']['row_indices']['factored']]],
             [[-1, []], [1, [D]], [-1, [u]], [-1, [v]]])
    need(bindings['schema'] == 'complete_pair_guard_ideal_bindings_v1' and bindings['identities'] == identities, 'all19 ideal bindings exactly')
    return dict(body_coordinates=nb, body_rows=nr, scalar_graphs=len(cert['retained_scalar_variables']),
                separate_product_graphs=len(cert['product_predicates']), source_variables=len(source['variables']),
                source_rows=len(source['residuals']), ideal_identities=len(identities), power_ports=len(ports), unused_body=unused)


def polynomial_check(equation, delivered, delivered_metrics):
    p = expansion(equation)
    need(delivered == dict(schema='sparse_integer_polynomial_v1', domain=equation['domain'],
                           variables=len(equation['variables']), terms=terms(p)), 'every complete quartic coefficient')
    need(metrics(equation, p) == delivered_metrics, 'entire independent polynomial census')
    need(degree(p) == 4, 'actual exact quartic degree')
    return p


def projection_check(source, output, cert, options):
    need(cert['schema'] == 'integer_quadratic_elimination_v1'
         and cert['input_sha256'] == sha256(canonical(source)).hexdigest()
         and cert['output_sha256'] == sha256(canonical(output)).hexdigest(), 'exact projection endpoints')
    rows = {i: poly(row['terms']) for i, row in enumerate(source['residuals'])}
    live = set(range(len(source['variables'])));deleted = set()
    for step in cert['steps']:
        row, variable = step['row_id'], step['variable'];p = poly(step['restoration'])
        need(row in rows and variable in live and variable not in deleted, 'valid unique monic deletion')
        need(step['name'] == source['variables'][variable]['name'] and step['kind'] == source['variables'][variable].get('kind'), 'restoration coordinate metadata')
        need(all(v in live and v != variable for m in p for v in m), 'integral restoration has only live dependencies')
        need(degree(p) <= 2 and step['restoration_degree'] == degree(p), 'quadratic integral restoration')
        cap = options['affine_support'] if degree(p) <= 1 and options['affine_support'] is not None else options['max_support']
        need(len(p) <= cap, 'actual support cap')
        target = {(variable,): 1}
        for m, c in p.items():target[m] = target.get(m, 0) - c
        target = {m: c for m, c in target.items() if c}
        need(rows[row] == target or rows[row] == {m: -c for m, c in target.items()}, 'deleted row exactly monic definition')
        if degree(p) == 2:
            need(all(variable not in m or len(m) == 1 for i, q in rows.items() if i != row for m in q), 'no nonlinear escape of quadratic restoration')
        transformed = {}
        for i, q in rows.items():
            if i != row:
                q = replace(q, variable, p);need(degree(q) <= 2, 'every substitution remains quadratic')
                if q:transformed[i] = q
        rows = transformed;live.remove(variable);deleted.add(variable)
    used = sorted({v for q in rows.values() for m in q for v in m});unused = sorted(live - set(used))
    need(cert['retained_original_variables'] == used and cert['unconstrained_removed'] == unused
         and cert['retained_original_rows'] == sorted(rows), 'whole retained/deleted/unconstrained partition')
    need(set(used) | set(unused) | deleted == set(range(len(source['variables']))), 'all input coordinates partitioned')
    vm = {v: i for i, v in enumerate(used)}
    expected_rows = [dict(label=source['residuals'][i]['label'], terms=remap(terms(q), vm)) for i, q in sorted(rows.items())]
    need(output['variables'] == [source['variables'][v] for v in used] and output['residuals'] == expected_rows, 'entire projected literal and variable map')
    need(all(set(m) <= set(range(len(used))) for row in output['residuals'] for _, m in row['terms']), 'projected variable bounds')
    need(set(range(len(used))) == {v for row in output['residuals'] for _, m in row['terms'] for v in m}, 'every projected coordinate actually used')
    need(output['domain'] == 'unrestricted integers', 'integer-domain projection')
    need({k:v for k,v in output.items() if k not in ['variables','residuals','metrics','elimination']}
         == {k:v for k,v in source.items() if k not in ['variables','residuals']}, 'whole projected nonmetric signature')
    p = expansion(output)
    exact = dict(expanded_monomials=len(p), exact_degree=degree(p),
                 max_abs_expanded_coefficient=max((abs(c) for c in p.values()), default=0),
                 max_abs_row_coefficient=max((abs(c) for row in output['residuals'] for c,_ in row['terms']), default=0))
    expected_metrics = dict(input_variables=len(source['variables']), output_variables=len(used),
        input_rows=len(source['residuals']), output_rows=len(rows), eliminated_coordinates=len(deleted),
        unconstrained_removed=len(unused),
        by_restoration_degree=dict(Counter(str(s['restoration_degree']) for s in cert['steps'])),
        by_kind=dict(Counter(s['kind'] for s in cert['steps'])),
        max_output_row_terms=max((len(q) for q in rows.values()), default=0), **options, **exact)
    need(cert['metrics'] == expected_metrics, 'every engine statistic independently reconstructed')
    need(output['metrics'] == dict(variables=len(used), quadratic_rows=len(rows),
                                  variable_kinds=dict(Counter(v.get('kind') for v in output['variables'])), **exact), 'whole projected metrics')
    need(output['elimination'] == dict(method='integral monic quadratic substitution',
                                      certificate='terminal_elimination_certificate.json'), 'actual certificate filename and method')
    def evaluate(p, values):
        result = 0
        for m, c in p.items():
            for v in m:c *= values[v]
            result += c
        return result
    # Signed fixtures test both composition directions of the actual restoration stack.
    for offset in [0, 3]:
        retained_values = {i: (i + offset) % 5 - 2 for i in range(len(used))}
        values = {old: retained_values[new] for new, old in enumerate(used)}
        values.update({v: 0 for v in unused})  # explicit arbitrary inverse choice for EVERY free coordinate
        for step in reversed(cert['steps']):values[step['variable']] = evaluate(poly(step['restoration']), values)
        need(set(values) == set(range(len(source['variables']))), 'whole signed inverse initializes all coordinates')
        surviving = {old: new for new, old in enumerate(sorted(rows))}
        for i, row in enumerate(source['residuals']):
            rhs = evaluate(poly(output['residuals'][surviving[i]]['terms']), retained_values) if i in surviving else 0
            need(evaluate(poly(row['terms']), values) == rhs, 'complete signed forward/reverse residual fixture')
    return dict(restorations=len(deleted), unconstrained_removed=unused, retained=len(used), signed_reverse_fixtures=2,
                expected_engine_verification=expected_metrics | dict(status='PASS', verified_steps=len(deleted),
                                                                    output_variables=len(used), output_rows=len(rows)))


def translation_check(original, translated, cert):
    expected = [[i, -1] for i, v in enumerate(original['variables'])
                if v['name'].startswith('crt.encoded') or v['name'] in ('t0', 'M0') or v['name'].endswith('minus1')]
    need(cert == dict(schema='integral_translation_v1', input_sha256=sha256(canonical(original)).hexdigest(),
                      output_sha256=sha256(canonical(translated)).hexdigest(), shifts=expected,
                      convention='old_coordinate = new_coordinate + shift', inverse='new_coordinate = old_coordinate - shift'), 'complete integral translation certificate')
    need(original['variables'] == translated['variables'], 'translation coordinate metadata')
    meta = {k:deepcopy(v) for k,v in original.items() if k not in ['variables','residuals','metrics','elimination']}
    meta['variant'] += ':integral_translation'
    need({k:v for k,v in translated.items() if k not in ['variables','residuals']} == meta,
         'whole translated signature and fixed provenance')
    for old, new in zip(original['residuals'], translated['residuals']):
        p = poly(old['terms'])
        for v, s in expected:p = replace(p, v, {(v,): 1, (): s})
        need(new == dict(label=old['label'], terms=terms(p)), 'every forward translated coefficient')
        for v, s in expected:p = replace(p, v, {(v,): 1, (): -s})
        need(p == poly(old['terms']), 'every inverse translation coefficient')
    need(len(original['residuals']) == len(translated['residuals']), 'translation row count')
    return len(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    pins = load(HERE / 'SOURCE_PINS.json')
    for n, h in pins['parent_files'].items():need(digest(ROOT / n) == h, 'immutable parent ' + n)
    for n, h in pins['own_core'].items():need(digest(HERE / n) == h, 'whole author core ' + n)
    need(digest(HERE / 'vendor/terminal_elimination.py') == pins['engine_sha256'], 'engine bytes, never imported')
    manifest = load(ORDINARY / 'MANIFEST.json')
    need(digest(ORDINARY / 'MANIFEST.json') == pins['ordinary_manifest_sha256'], 'ordinary proof seal')
    need(set(manifest['files']) == {str(p.relative_to(ORDINARY)) for p in ORDINARY.rglob('*') if p.is_file() and p != ORDINARY / 'MANIFEST.json'}, 'closed ordinary inventory')
    for n, h in manifest['files'].items():need(digest(ORDINARY / n) == h, 'whole ordinary member')
    if (HERE / 'MANIFEST.json').exists():
        m = load(HERE / 'MANIFEST.json')['files'];need(set(m) == {str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p != HERE / 'MANIFEST.json'}, 'closed own inventory')
        for n, h in m.items():need(digest(HERE / n) == h, 'whole frozen own member')
    index = load(args.data / 'INDEX.json');mode = 'source-only' if args.source_only else 'full'
    need(index['schema'] == 'round14_pair_guard_release_v1' and index['mode'] == mode
         and index['configurations'] == CONFIGS and index['reviewed_engine_executed'] == (mode == 'full'), 'actual release stage/configurations')
    need(index['ordinary_manifest_sha256'] == pins['ordinary_manifest_sha256']
         and index['incoming_or_lean_executed'] is False and index['accepted_or_promoted_metrics_claimed'] is False, 'scoped release')
    need(set(index['files']) == {str(p.relative_to(args.data)) for p in args.data.rglob('*') if p.is_file() and p != args.data / 'INDEX.json'}, 'complete generated inventory')
    for n, h in index['files'].items():need(digest(args.data / n) == h, 'whole generated artifact ' + n)
    ordinary = load(ORDINARY / 'CERTIFICATE.json');results = {};rejects = []
    need(set(index['summaries']) == set(ordinary['variants']), 'all and only two source ancestries')
    def reject(label, callback):
        try:callback()
        except (ValueError, KeyError, IndexError):rejects.append(label)
        else:raise ValueError('accepted actual malformed artifact ' + label)
    for tag, cert in ordinary['variants'].items():
        directory = args.data / 'sources' / tag
        source, contract, bindings = [load(directory / n) for n in ['equation.json', 'BODY_GUARD_MAP.json', 'IDEAL_BINDINGS.json']]
        results[tag] = source_check(tag, cert, source, contract, bindings)
        need(index['summaries'][tag]['source_variables'] == len(source['variables'])
             and index['summaries'][tag]['source_rows'] == len(source['residuals']), 'actual source-only dimensions')
        need(set(index['summaries'][tag]['profiles']) == (set() if args.source_only else set(CONFIGS)), 'all requested profile families')
        def bad_source(label, change):
            s, c, b = deepcopy(source), deepcopy(contract), deepcopy(bindings);change(s, c, b)
            reject(tag + ':' + label, lambda:source_check(tag, cert, s, c, b))
        bad_source('body coefficient', lambda s,c,b:s['residuals'][0]['terms'][0].__setitem__(0, 123))
        bad_source('missing appended Horn map', lambda s,c,b:c['body_variable_map'].pop())
        bad_source('old auxiliary escape map', lambda s,c,b:c['body_variable_map'].append([c['excluded_old_guard_auxiliaries'][0], 0]))
        bad_source('one product factor', lambda s,c,b:s['residuals'][c['predicates'][-1]['row']]['terms'][0][1].__setitem__(0, 0))
        bad_source('merged pair products', lambda s,c,b:s['residuals'][c['predicates'][-1]['row']]['terms'][0][1].extend(c['predicates'][-2]['variables']))
        bad_source('guard sign', lambda s,c,b:s['residuals'][c['predicates'][0]['row']]['terms'][1].__setitem__(0, 1))
        bad_source('fresh triple reused', lambda s,c,b:c['predicates'][1].__setitem__('auxiliary', c['predicates'][0]['auxiliary']))
        bad_source('power port', lambda s,c,b:b['remapped_power_ports'][0]['output'][0][1].__setitem__(0, 0))
        bad_source('ideal cut', lambda s,c,b:b['identities'][0]['new_cuts'][0].__setitem__(0, -1))
        bad_source('unconstrained coordinate omitted', lambda s,c,b:c['unused_body_coordinates'].pop())
        if args.source_only:
            continue
        rawpoly = polynomial_check(source, load(directory / 'expanded_polynomial.json'), load(directory / 'METRICS.json'))
        profiles = {}
        for config, options in CONFIGS.items():
            directory = args.data / 'profiles' / tag / config
            eq, pc, delivered, m = [load(directory / n) for n in ['equation.json', 'terminal_elimination_certificate.json', 'expanded_polynomial.json', 'METRICS.json']]
            projection = projection_check(source, eq, pc, options);p = polynomial_check(eq, delivered, m)
            need(load(directory/'ENGINE_VERIFICATION.json') == projection.pop('expected_engine_verification'),
                 'entire engine report independently recollected')
            centered_dir = directory / 'centered'
            centered, tc, cp, cm = [load(centered_dir / n) for n in ['equation.json', 'translation_certificate.json', 'expanded_polynomial.json', 'METRICS.json']]
            shifts = translation_check(eq, centered, tc);q = polynomial_check(centered, cp, cm)
            for v, s in tc['shifts']:q = replace(q, v, {(v,): 1, (): -s})
            need(q == p, 'entire quartic inverse translation')
            need(index['summaries'][tag]['profiles'][config] == dict(plain=m, centered=cm), 'measured complete profile summaries')
            profiles[config] = dict(plain=m, centered=cm, projection=projection, translated_coordinates=shifts)
            if config == 'support16':
                def bad_profile(label, change):
                    e, c, pp, mm, ce, tt = deepcopy(eq), deepcopy(pc), deepcopy(delivered), deepcopy(m), deepcopy(centered), deepcopy(tc)
                    change(e,c,pp,mm,ce,tt)
                    def check():
                        projection_check(source,e,c,options);polynomial_check(e,pp,mm);translation_check(e,ce,tt)
                    reject(tag + ':' + label, check)
                def corrupt_restoration(e,c,p,m,ce,t):
                    step = next(s for s in c['steps'] if s['restoration'])
                    step['restoration'][0][0] += 1
                bad_profile('monic restoration', corrupt_restoration)
                bad_profile('unconstrained inverse omitted', lambda e,c,p,m,ce,t:c['unconstrained_removed'].pop())
                bad_profile('retained map', lambda e,c,p,m,ce,t:c['retained_original_variables'].__setitem__(0, -1))
                bad_profile('deleted row', lambda e,c,p,m,ce,t:c['steps'][0].__setitem__('row_id', -1))
                bad_profile('projected row coefficient', lambda e,c,p,m,ce,t:e['residuals'][0]['terms'][0].__setitem__(0, 999))
                bad_profile('quartic coefficient', lambda e,c,p,m,ce,t:p['terms'][0].__setitem__(0, 999))
                bad_profile('census height', lambda e,c,p,m,ce,t:m.__setitem__('height', m['height']+1))
                bad_profile('translation shift', lambda e,c,p,m,ce,t:t['shifts'][0].__setitem__(1, -2))
                bad_profile('translated row', lambda e,c,p,m,ce,t:ce['residuals'][0]['terms'][0].__setitem__(0, 999))
        results[tag]['profiles'] = profiles
        results[tag]['raw_literal_census'] = metrics(source, rawpoly)
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), stage=mode, variants=results,
                  rejected_actual_corruptions=rejects, ordinary_manifest_sha256=pins['ordinary_manifest_sha256'],
                  source_pins_sha256=digest(HERE/'SOURCE_PINS.json'), index_sha256=digest(args.data/'INDEX.json'),
                  producer_or_optimizer_or_parent_or_incoming_or_lean_imported=False,
                  accepted_or_promoted_metrics_claimed=False,
                  scope='Finite literal/complete coefficient premises; ordinary zero-existence composition is PROOF.md and its sealed parent.')
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output.exists():need(args.output.read_text() == text, 'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS', stage=mode, variants=len(results), actual_corruptions=len(rejects), optimized_python=bool(sys.flags.optimize)), sort_keys=True))


if __name__ == '__main__':
    main()
