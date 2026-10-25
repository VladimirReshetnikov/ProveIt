#!/usr/bin/env python3
"""Independent SOURCE ONLY audit; HOLD until both reviews and root release."""
import argparse
from collections import defaultdict
import copy
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / 'research/signed-pell-cap-refined-source'
ORDINARY = ROOT / 'research/signed-pell-cap-refined-scalar-product'
PARENT_SEAL = '73a5b427338c33cb5ff0365fc64a994b796b16837d9bdc2a987d63d5eef8ed51'
ORDINARY_SEAL = 'be2a7ff725502344d862af1fdca0744fc64272840ec8947f214b7deee3773b0e'
NAMES = ['source.json', 'guarded.json', 'domain.json', 'TRANSFORM.json', 'CALIBRATION_BINDING.json']
CALL_ROWS = [226, 234, 239, 247, 253, 258, 266, 271, 276, 281, 286, 291, 296, 301, 306, 311, 316, 321]
DROP_ROWS = {335, 339, 340, 341, 342, 343, 344, 345, 346, 347}
DROP_AUX = {402, 403, 404} | set(range(414, 441))
OMIT = {1, 6, 7, 8, 9, 10, 11, 12, 13, 14}
CHRONOLOGY = ['temporary_helper_normalization', 'absolute_frame_and_nonzero_t',
              'signed_A_primary_pool', 'q_support_at_t', 'same_pair_base_one_then_F',
              'four_q_power_denominators', 'successor_residues_and_signed_indices',
              'reciprocal_last_scalar', 'strict_eight_factor_product',
              'restore_graphs_on_original_unnormalized_body', 'refined_calibration']


def need(ok, text):
    if not ok:
        raise ValueError(text)


def read(path):
    return json.loads(path.read_bytes())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def poly(items):
    out = defaultdict(int)
    for c, m in items:
        out[tuple(sorted(m))] += c
    return {m: c for m, c in out.items() if c}


def terms(p):
    return [[c, list(m)] for m, c in sorted(p.items()) if c]


def add(*ps):
    out = defaultdict(int)
    for p in ps:
        for m, c in p.items():
            out[m] += c
    return {m: c for m, c in out.items() if c}


def scale(p, c):
    return {m: c * v for m, v in p.items() if c * v}


def mul(p, q):
    out = defaultdict(int)
    for m, c in p.items():
        for n, d in q.items():
            out[tuple(sorted(m + n))] += c * d
    return {m: c for m, c in out.items() if c}


def V(i):
    return {(i,): 1}


def C(c):
    return {(): c} if c else {}


def substitute(p, v, value):
    result = {}
    for m, c in p.items():
        term = C(c)
        for i in m:
            term = mul(term, value if i == v else V(i))
        result = add(result, term)
    return result


def moved(p, mapping):
    return poly([[c, [mapping[i] for i in m]] for m, c in p.items()])


def graph(expression, auxiliary):
    a, b, c = auxiliary
    return add(expression, {(a, a): -1, (b, b): -1, (c, c): -1, (c,): -1})


def authenticate():
    pins = read(HERE / 'SOURCE_PINS.json')
    for section, base in [('files', ROOT), ('core', HERE)]:
        for name, expected in pins[section].items():
            need(digest(base / name) == expected, 'whole pinned file ' + name)
    for name, expected in pins['closed_dependencies'].items():
        directory = ROOT / name
        need(digest(directory / 'MANIFEST.json') == expected, 'closed dependency ' + name)
        actual = {str(p.relative_to(directory)): digest(p) for p in directory.rglob('*')
                  if p.is_file() and p != directory / 'MANIFEST.json'}
        need(read(directory / 'MANIFEST.json')['files'] == actual, 'whole closed inventory ' + name)
    need(pins['closed_dependencies'].get(str(PARENT.relative_to(ROOT))) == PARENT_SEAL,
         'exact refined source seal')
    need(pins['closed_dependencies'].get(str(ORDINARY.relative_to(ROOT))) == ORDINARY_SEAL,
         'exact complete ordinary theorem seal')
    if (HERE / 'MANIFEST.json').exists():
        actual = {str(p.relative_to(HERE)): digest(p) for p in HERE.rglob('*')
                  if p.is_file() and p != HERE / 'MANIFEST.json'}
        need(read(HERE / 'MANIFEST.json')['files'] == actual, 'complete sealed product packet')
    return pins


def expected():
    body, old, domain = [read(PARENT / n) for n in ['source.json', 'guarded.json', 'domain.json']]
    interface, parent_plan = read(ORDINARY / 'INTERFACE.json'), read(PARENT / 'TRANSFORM.json')
    need(len(body['variables']) == 399 and len(body['residuals']) == 334, 'fixed whole parent body')
    oldvars = [i for i in range(len(old['variables'])) if i not in DROP_AUX]
    vm = {i: j + (7 if i >= 399 else 0) for j, i in enumerate(oldvars)}
    oldrows = [i for i in range(len(old['residuals'])) if i not in DROP_ROWS]
    rm = {i: j + (7 if i >= 334 else 0) for j, i in enumerate(oldrows)}
    fresh = [dict(name='scalar_product.p' + str(j), kind='gate') for j in range(2, 9)]
    products, definitions = [], []
    for offset in range(7):
        v = 399 + offset
        factor = mul(add(V(16), C(1)), add(V(17), C(1))) if offset == 0 else mul(V(v - 1), add(V(17 + offset), C(1)))
        definitions.append(dict(label='scalar_product.p' + str(offset + 2) + '_definition',
                                terms=terms(add(V(v), scale(factor, -1)))))
        products.append(dict(name='p' + str(offset + 2), coordinate=v, row=334 + offset))
    source = dict(schema='refined_cap_scalar_product_body_v1', domain='unrestricted integers',
                  variant='refined_signed_cap_eight_factor_scalar_product_source_only',
                  polynomial='sum of squares of all residuals',
                  variables=copy.deepcopy(body['variables']) + fresh,
                  residuals=copy.deepcopy(body['residuals']) + definitions,
                  parent_source_manifest_sha256=PARENT_SEAL, ordinary_manifest_sha256=ORDINARY_SEAL)
    guarded = copy.deepcopy(source)
    guarded['variables'] = ([copy.deepcopy(old['variables'][i]) for i in oldvars[:399]] + fresh +
                            [copy.deepcopy(old['variables'][i]) for i in oldvars[399:]])
    def oldrow(i):
        result = copy.deepcopy(old['residuals'][i])
        result['terms'] = terms(moved(poly(result['terms']), vm))
        return result
    guarded['residuals'] = [oldrow(i) for i in oldrows[:334]] + definitions + [oldrow(i) for i in oldrows[334:]]
    auxiliary = list(range(len(guarded['variables']), len(guarded['variables']) + 3))
    strict = dict(kind='strict_index_product', expression=[[-1, []], [1, [405]]], product_coordinate=405,
                  factors=[dict(coordinate=i, shift=1) for i in range(16, 24)],
                  auxiliary=auxiliary, row=len(guarded['residuals']))
    guarded['variables'] += [dict(name='scalar_product_positive.' + s, kind='integer_guard') for s in ['a', 'b', 'c']]
    guarded['residuals'].append(dict(label='domain_guard.scalar_product_positive',
                                    terms=terms(graph(poly(strict['expression']), auxiliary))))
    kept, removed = [], []
    for spec in domain['guards']:
        if spec['row'] in DROP_ROWS:
            removed.append(copy.deepcopy(spec))
            continue
        new = copy.deepcopy(spec)
        new.update(row=rm[spec['row']], auxiliary=[vm[i] for i in spec['auxiliary']],
                   expression=terms(moved(poly(spec['expression']), vm)))
        for key in ['coordinate', 'product_coordinate']:
            if key in new:
                new[key] = vm[new[key]]
        if 'pair' in new:
            new['pair'] = [vm[i] for i in new['pair']]
        kept.append(new)
    kept.append(strict)
    occurrences = {str(v): [i for i, r in enumerate(old['residuals']) if any(v in m for c, m in r['terms'])]
                   for v in sorted(DROP_AUX)}
    plan = dict(schema='refined_cap_scalar_product_literal_map_v1',
                parent_manifest_sha256=PARENT_SEAL, ordinary_manifest_sha256=ORDINARY_SEAL,
                old_body_to_new=[[i, i] for i in range(399)],
                old_guarded_to_new=[[i, vm[i]] for i in oldvars],
                old_row_to_new=[dict(old_row=i, new_row=rm.get(i),
                                    status='omitted_scalar_graph' if i in DROP_ROWS else 'identical')
                                for i in range(len(old['residuals']))],
                omitted_original_guard_indices=sorted(OMIT), removed_graphs=removed,
                removed_private_coordinates=sorted(DROP_AUX), complete_omitted_auxiliary_occurrences=occurrences,
                product_gates=products, new_product_graph=strict,
                all18_actual_power_requests=copy.deepcopy(interface['all18_actual_power_requests']),
                all15_signed_targets=copy.deepcopy(parent_plan['all_original_seeds']),
                all37_frame_atoms=copy.deepcopy(parent_plan['all37_frame_atoms']),
                native_front_parent=parent_plan['native_front_new'], native_front_new=parent_plan['native_front_new'],
                helper_reflection=parent_plan['reflection'], helper_normalization_is_temporary=True,
                whole_refined_body_pointwise_fixed=True, retained_witness_values_preserved_under_map=True,
                h_changes_in_product_maps=False, A_or_C_positive_assumed=False, chronology=CHRONOLOGY,
                optimizer_factorization_projection_executed=False, accepted_projected_frontier_claim=False)
    result = {'source.json': source, 'guarded.json': guarded,
              'domain.json': dict(schema='refined_cap_scalar_product_domain_v1', guards=kept), 'TRANSFORM.json': plan}
    result['CALIBRATION_BINDING.json'] = dict(
        schema='refined_cap_product_ordinary_source_calibration_v1',
        parent_manifest_sha256=PARENT_SEAL, ordinary_manifest_sha256=ORDINARY_SEAL,
        parent_calibration_sha256=digest(PARENT / 'CALIBRATION_BINDING.json'),
        source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
        generated_source_files={n: hashlib.sha256(encoded(v)).hexdigest() for n, v in result.items()},
        formal_native_contracts=read(PARENT / 'CALIBRATION_BINDING.json')['formal_native_contracts'],
        native_front_parent=parent_plan['native_front_new'], native_front_new=parent_plan['native_front_new'],
        witness_maps='Keep original unnormalized refined body and retained witnesses; restore ten old triples, or adjoin exact products and their strict graph. Both maps keep h and signed A/C.',
        ordinary_soundness_and_positive_completeness='Compose sealed pointwise refined scalar-product theorem with complete sealed refined-source calibration only after restoring its ten graph rows.',
        whole_refined_body_pointwise_fixed=True, new_formal_Lean_theorem_claimed=False,
        optimizer_factorization_projection_or_quartic_executed=False)
    return result, body, old, vm, rm


def macro_bindings(source, requests, seeds):
    names = {v['name']: i for i, v in enumerate(source['variables'])}
    definitions = {}
    cap_names = {'index_cap.AY', 'index_cap.Y2', 'index_cap.BR'}
    for i, variable in enumerate(source['variables']):
        special, cap = variable['name'] == 'index_addition.D', variable['name'] in cap_names
        if variable['kind'] != 'gate' and not special and not cap:
            continue
        labels = ['index_addition.D_definition'] if special else [variable['name']] if cap else ['addition', 'multiplication']
        found = []
        for row in source['residuals']:
            if row['label'] not in labels:
                continue
            p = poly(row['terms']); coefficient = p.get((i,), 0)
            if coefficient in ([-1, 1] if special else [1]) and not any(i in m for m in p if m != (i,)):
                found.append(scale(add(p, {(i,): -coefficient}), -coefficient))
        if len(found) == 1:
            definitions[i] = found[0]
    boundary = (set(range(246)) | set(range(376, 386)) |
                {246, 247, 250, 251, 252, 253, 255, 375, 386, 387, 390, 391, 393, 394, 395} |
                {i for s in seeds for i in s['pair']} |
                {i for i, v in enumerate(source['variables']) if v['name'].startswith('pow') and v['name'].endswith('.quotient')} |
                {names['base' + str(i) + '.T'] for i in range(5)})
    def expand(p, stop=boundary):
        memo, busy = {}, set()
        def value(i):
            if i in stop:
                return V(i)
            if i not in memo:
                need(i in definitions and i not in busy, 'acyclic complete macro gate ' + str(i))
                busy.add(i); memo[i] = walk(definitions[i]); busy.remove(i)
            return memo[i]
        def walk(q):
            result = {}
            for m, c in q.items():
                term = C(c)
                for i in m:
                    term = mul(term, value(i))
                result = add(result, term)
            return result
        return walk(p)
    A = V(246); D = add(mul(A, A), C(-1))
    for s in seeds:
        rows = [r for r in source['residuals'] if r['label'] == s['prefix'] + '.norm1']
        need(len(rows) == 1, 'unique actual primary norm')
        x, y = map(V, s['pair'])
        need(expand(poly(rows[0]['terms'])) == add(mul(x, x), scale(mul(D, mul(y, y)), -1), C(-1)), 'whole primary norm')
    for call, request in enumerate(requests):
        i = CALL_ROWS[call]; row = source['residuals'][i]
        need(request['call'] == call and request['row'] == i and row['label'] == request['label'] == 'pow' + str(call) + '.power_congruence', 'actual call/row/label membership')
        need(row == request['complete_row'], 'whole actual request row')
        n, output = poly(request['ports']['base']), poly(request['ports']['output'])
        if call == 6:
            need(poly(request['ports']['exponent']) == add(poly(seeds[0]['target']), C(1)) and request['primary_pair'] is None, 'actual derived successor target')
            X, Y = map(V, seeds[0]['pair'])
            x, y = add(mul(A, X), mul(D, Y)), add(X, mul(A, Y))
        else:
            seed = next(s for s in seeds if call in s['calls'])
            need(seed['pair'] == request['primary_pair'] and seed['target'] == request['ports']['exponent'], 'actual pair/target membership')
            x, y = map(V, seed['pair'])
        group = next(j for j in range(5) if poly(requests[j]['ports']['base']) == n)
        modulus = V(names['base' + str(group) + '.T'])
        quotient = V(names['pow' + str(call) + '.quotient'])
        want = add(x, mul(add(n, scale(A, -1)), y), scale(output, -1), scale(mul(modulus, quotient), -1))
        need(expand(poly(row['terms'])) == want, 'complete actual lowered unsquared request')
    for group in range(5):
        row = next(r for r in source['residuals'] if r['label'] == 'base' + str(group) + '.T_definition')
        n = poly(requests[group]['ports']['base'])
        want = add(scale(V(names['base' + str(group) + '.T']), -1), scale(mul(A, n), 2), scale(mul(n, n), -1), C(-1))
        need(expand(poly(row['terms']), boundary - {175}) == want, 'whole shared signed-base modulus')
    return dict(all15_norms=True, all18_actual_call_memberships=True, all18_unsquared_requests=True,
                all5_shared_moduli=True, signed_derived_t_plus_one=True)


def validate(artifacts):
    exp, body, old, vm, rm = expected()
    need(set(artifacts) == set(exp), 'complete five-artifact inventory')
    for name, value in exp.items():
        need(artifacts[name] == value, 'entire independently reconstructed artifact ' + name)
    source, guarded, domain, plan = [artifacts[n] for n in NAMES[:4]]
    need(source['domain'] == guarded['domain'] == 'unrestricted integers', 'unrestricted domains')
    need(source['variables'][:399] == body['variables'] and source['residuals'][:334] == body['residuals'], 'whole original body fixed')
    need(len({v['name'] for v in guarded['variables']}) == len(guarded['variables']), 'fresh unique coordinate names')
    for row in guarded['residuals']:
        need(row['terms'] == terms(poly(row['terms'])), 'canonical complete coefficient list')
        need(all(type(c) is int and len(m) <= 2 and all(type(i) is int and 0 <= i < len(guarded['variables']) for i in m)
                 for c, m in row['terms']), 'all integer quadratic residuals')
    need({i for r in guarded['residuals'] for c, m in r['terms'] for i in m} == set(range(len(guarded['variables']))), 'every emitted coordinate occurs')
    for i, j in rm.items():
        copied = copy.deepcopy(old['residuals'][i]); copied['terms'] = terms(moved(poly(copied['terms']), vm))
        need(copied == guarded['residuals'][j], 'every retained complete old residual identity')
    newvars = set(range(399, 406)) | set(plan['new_product_graph']['auxiliary'])
    newrows = set(range(334, 341)) | {plan['new_product_graph']['row']}
    need(set(vm) == set(range(len(old['variables']))) - DROP_AUX and len(set(vm.values())) == len(vm), 'old coordinate bijection')
    need(set(vm.values()) | newvars == set(range(len(guarded['variables']))) and not set(vm.values()) & newvars, 'complete new coordinate namespace')
    need(set(rm) == set(range(len(old['residuals']))) - DROP_ROWS and set(rm.values()) | newrows == set(range(len(guarded['residuals']))), 'complete row bijection')
    for spec in plan['removed_graphs']:
        need(spec in read(ORDINARY / 'INTERFACE.json')['omitted_graphs'], 'exact removed graph record')
        for v in spec['auxiliary']:
            need([i for i, r in enumerate(old['residuals']) if any(v in m for c, m in r['terms'])] == [spec['row']], 'whole removed graph privacy')
    for spec in domain['guards']:
        need(poly(guarded['residuals'][spec['row']]['terms']) == graph(poly(spec['expression']), spec['auxiliary']), 'complete retained/new Legendre graph')
        for v in spec['auxiliary']:
            need([i for i, r in enumerate(guarded['residuals']) if any(v in m for c, m in r['terms'])] == [spec['row']], 'whole graph witness privacy')
    restoration = {}
    for offset in range(7):
        v = 399 + offset
        p = poly(source['residuals'][334 + offset]['terms'])
        need(p.pop((v,), 0) == 1 and not any(v in m for m in p), 'unique monic fresh product')
        q = scale(p, -1)
        for earlier, value in restoration.items():
            q = substitute(q, earlier, value)
        restoration[v] = q
        hits = [i for i, r in enumerate(guarded['residuals']) if any(v in m for c, m in r['terms'])]
        need(hits == [334 + offset, 335 + offset if offset < 6 else plan['new_product_graph']['row']], 'complete fresh product occurrence map')
    product = C(1)
    for i in range(16, 24):
        product = mul(product, add(V(i), C(1)))
    need(restoration[405] == product, 'whole eight-factor polynomial identity')
    interface = read(ORDINARY / 'INTERFACE.json')
    for i, row in interface['literal_rows'].items():
        need(source['residuals'][int(i)] == row, 'every ordinary literal interface row')
    for cut in interface['successor_residue_identities']:
        p = add(*[mul(poly(t['multiplier']), poly(source['residuals'][t['row']]['terms'])) for t in cut['source_ideal_combination']])
        need(p == poly(cut['identity_residual']), 'whole successor source ideal')
    atoms = plan['all37_frame_atoms']; W = V(245)
    need(poly(source['residuals'][333]['terms']) == add(W, C(-4), *[scale(mul(poly(a['affine']), poly(a['affine'])), -2) for a in atoms]), 'whole original square frame')
    front = set(plan['native_front_new'])
    need(all(i in front and i < 399 for a in atoms for c, m in a['affine'] for i in m), 'complete original native front and new-gate exclusion from frame')
    for request in plan['all18_actual_power_requests']:
        for key in ['base', 'exponent', 'output']:
            need(any(poly(request['ports'][key]) == poly(a['affine']) for a in atoms), 'every one of54 actual bounded ports')
    reflection = {int(i): poly(p) for i, p in plan['helper_reflection'].items()}
    def reflect(p):
        for i, value in reflection.items():
            p = substitute(p, i, value)
        return p
    for i in range(len(guarded['variables'])):
        need(reflect(reflect(V(i))) == V(i), 'complete helper coordinate involution')
    for i, row in enumerate(guarded['residuals']):
        need(reflect(poly(row['terms'])) == scale(poly(row['terms']), -1 if i in [205, 322] else 1), 'every full row helper identity')
    for i in [1] + list(range(16, 25)):
        need(reflect(V(i)) == V(i), 'each recovered scalar fixed by temporary reflection')
    macros = macro_bindings(source, plan['all18_actual_power_requests'], plan['all15_signed_targets'])
    # Universal signed-center identities, not values sampled on Pell solutions.
    A, n, X, Y = map(V, range(4))
    D = add(mul(A, A), C(-1)); modulus = add(scale(mul(A, n), 2), scale(mul(n, n), -1), C(-1))
    H, J = add(X, mul(add(n, scale(A, -1)), Y)), add(X, scale(mul(add(n, scale(A, -1)), Y), -1))
    norm = add(mul(X, X), scale(mul(D, mul(Y, Y)), -1), C(-1))
    need(add(mul(H, J), C(-1), scale(mul(modulus, mul(Y, Y)), -1)) == norm, 'universal signed branch product identity')
    xp, yp = add(mul(A, X), mul(D, Y)), add(X, mul(A, Y))
    need(add(xp, mul(add(n, scale(A, -1)), yp), scale(mul(n, H), -1), scale(mul(modulus, Y), -1)) == {}, 'universal signed recurrence identity')
    # Supplemental signed fixtures do not assert zeros or scalar signs.
    for phase in [2, 7]:
        values = [((i + phase) % 13 - 6) * (-1 if i % 2 else 1) for i in range(len(guarded['variables']))]
        def evaluate(p, vector):
            total = 0
            for m, c in p.items():
                term = c
                for i in m:
                    term *= vector[i]
                total += term
            return total
        for v, q in restoration.items():
            values[v] = evaluate(q, values)
        previous = [0] * len(old['variables'])
        for i, j in vm.items():
            previous[i] = values[j]
        for i, j in rm.items():
            need(evaluate(poly(old['residuals'][i]['terms']), previous) == evaluate(poly(guarded['residuals'][j]['terms']), values), 'signed complete retained-row fixture')
        need(all(evaluate(poly(source['residuals'][r]['terms']), values) == 0 for r in range(334, 341)), 'signed unique product fixtures')
    return dict(whole_old_body=True, whole_old_rows=True, whole_coordinate_and_row_bijections=True,
                all_retained_and_new_graphs=True, all_removed_and_retained_witness_privacy=True,
                exact_eight_factor_polynomial=True, whole37_atom_frame=True, all54_bounded_ports=True,
                all11_source_ideals=True, full_helper_reflection=True, actual_macro_interfaces=macros,
                signed_retained_row_fixtures=2, universal_signed_power_identities=True,
                calibration=artifacts['CALIBRATION_BINDING.json'],
                chronology=CHRONOLOGY, source_only=True, accepted_projected_frontier_claim=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, default=HERE)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); pins = authenticate()
    artifacts = {n: read(args.packet / n) for n in NAMES}
    for n, value in artifacts.items():
        need((args.packet / n).read_bytes() == encoded(value), 'whole canonical artifact bytes ' + n)
    evidence = validate(artifacts); rejected = []
    def trial(label, change):
        altered = copy.deepcopy(artifacts); change(altered)
        try:
            validate(altered)
        except (ValueError, KeyError, TypeError, IndexError, StopIteration):
            rejected.append(label)
        else:
            raise ValueError('actual corruption accepted ' + label)
    for i in [0, 191, 217, 218, 226, 253, 266, 291, 306, 333, 334, 340]:
        trial('actual source residual ' + str(i), lambda d, i=i: d['source.json']['residuals'][i]['terms'][0].__setitem__(0, 999))
    trial('old body metadata', lambda d: d['source.json']['variables'][1].__setitem__('name', 'changed'))
    trial('unrestricted domain', lambda d: d['guarded.json'].__setitem__('domain', 'nonnegative integers'))
    trial('retained witness metadata', lambda d: d['guarded.json']['variables'][406].__setitem__('name', 'changed'))
    trial('new strict graph coefficient', lambda d: d['guarded.json']['residuals'][-1]['terms'][0].__setitem__(0, 0))
    trial('new threshold', lambda d: d['domain.json']['guards'][-1]['expression'][0].__setitem__(0, 0))
    trial('wrong product factor', lambda d: d['domain.json']['guards'][-1]['factors'][0].__setitem__('shift', 0))
    trial('private graph escape', lambda d: d['guarded.json']['residuals'][0]['terms'].append([1, [475]]))
    trial('missing old coordinate map', lambda d: d['TRANSFORM.json']['old_guarded_to_new'].pop())
    trial('wrong old row map', lambda d: d['TRANSFORM.json']['old_row_to_new'][335].__setitem__('new_row', 335))
    trial('wrong removed auxiliary set', lambda d: d['TRANSFORM.json']['removed_private_coordinates'].pop())
    trial('wrong actual call11 row', lambda d: d['TRANSFORM.json']['all18_actual_power_requests'][11].__setitem__('row', 296))
    trial('wrong actual call14 row', lambda d: d['TRANSFORM.json']['all18_actual_power_requests'][14].__setitem__('row', 311))
    trial('wrong actual call label', lambda d: d['TRANSFORM.json']['all18_actual_power_requests'][14].__setitem__('label', 'pow15.power_congruence'))
    trial('wrong actual output port', lambda d: d['TRANSFORM.json']['all18_actual_power_requests'][14]['ports']['output'][0][1].__setitem__(0, 229))
    trial('new gate in frame', lambda d: d['TRANSFORM.json']['all37_frame_atoms'][0]['affine'].append([1, [399]]))
    for key, value in [('helper_normalization_is_temporary', False), ('whole_refined_body_pointwise_fixed', False), ('h_changes_in_product_maps', True), ('A_or_C_positive_assumed', True)]:
        trial('wrong ordinary boundary ' + key, lambda d, key=key, value=value: d['TRANSFORM.json'].__setitem__(key, value))
    trial('wrong chronology', lambda d: d['TRANSFORM.json']['chronology'].reverse())
    trial('wrong ordinary seal', lambda d: d['CALIBRATION_BINDING.json'].__setitem__('ordinary_manifest_sha256', '0' * 64))
    trial('missing generated binding', lambda d: d['CALIBRATION_BINDING.json']['generated_source_files'].pop('guarded.json'))
    trial('missing source artifact', lambda d: d.pop('domain.json'))
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), evidence=evidence,
                  actual_corruptions_rejected=rejected, source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
                  generated={n: digest(args.packet / n) for n in NAMES})
    target = args.output.resolve()
    need(not any(target.is_relative_to((ROOT / n).resolve()) for n in pins['closed_dependencies']), 'never write a closed dependency')
    need(not (HERE / 'MANIFEST.json').exists() or not target.is_relative_to(HERE), 'receipt outside sealed packet')
    data = encoded(result)
    need(not args.output.is_symlink() and (not args.output.exists() or args.output.read_bytes() == data), 'refuse different existing receipt')
    args.output.parent.mkdir(parents=True, exist_ok=True); args.output.write_bytes(data)
    print(data.decode(), end='')


if __name__ == '__main__':
    main()
