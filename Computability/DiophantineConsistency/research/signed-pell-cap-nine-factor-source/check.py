#!/usr/bin/env python3
"""Independent nine-factor SOURCE ONLY audit; CODE ONLY/HOLD for review."""
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
PARENT = ROOT / 'research/signed-pell-cap-refined-product-source'
ORDINARY = ROOT / 'research/signed-pell-cap-nine-factor-fused'
PARENT_SEAL = 'de311c82c61e7fee99e816c971256d662a28e620c51807ca7d5ef3611240ea93'
ORDINARY_SEAL = '836c87b375d2049c44548e999a9b271b40805211bcbb5f01678f108a2c53a60d'
DROP_ROWS = {344, 364}
DROP_AUX = {415, 416, 417, 475, 476, 477}
CALL_ROWS = [226, 234, 239, 247, 253, 258, 266, 271, 276, 281, 286, 291, 296, 301, 306, 311, 316, 321]
NAMES = ['source.json', 'guarded.json', 'domain.json', 'TRANSFORM.json', 'CALIBRATION_BINDING.json']


def need(ok, why):
    if not ok:
        raise ValueError(why)


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
        folder = ROOT / name
        need(digest(folder / 'MANIFEST.json') == expected, 'closed dependency seal ' + name)
        declared = read(folder / 'MANIFEST.json')['files']
        actual = {str(p.relative_to(folder)): digest(p) for p in folder.rglob('*')
                  if p.is_file() and p != folder / 'MANIFEST.json'}
        members = {n: dict(bytes=(folder / n).stat().st_size, sha256=h)
                   if isinstance(declared.get(n), dict) else h for n, h in actual.items()}
        need(declared == members, 'complete closed dependency inventory ' + name)
    need(pins['closed_dependencies'].get(str(PARENT.relative_to(ROOT))) == PARENT_SEAL,
         'exact complete parent source seal')
    need(pins['closed_dependencies'].get(str(ORDINARY.relative_to(ROOT))) == ORDINARY_SEAL,
         'exact complete fused-nine ordinary seal')
    if (HERE / 'MANIFEST.json').exists():
        actual = {str(p.relative_to(HERE)): digest(p) for p in HERE.rglob('*')
                  if p.is_file() and p != HERE / 'MANIFEST.json'}
        need(read(HERE / 'MANIFEST.json')['files'] == actual, 'complete sealed source packet')
    return pins


def expected():
    body, old, domain = [read(PARENT / n) for n in ['source.json', 'guarded.json', 'domain.json']]
    interface = read(ORDINARY / 'INTERFACE.json')
    need(len(body['variables']) == 406 and len(body['residuals']) == 341, 'whole body boundary')
    kept_vars = [i for i in range(len(old['variables'])) if i not in DROP_AUX]
    kept_rows = [i for i in range(len(old['residuals'])) if i not in DROP_ROWS]
    vm, rm = {i: j for j, i in enumerate(kept_vars)}, {i: j for j, i in enumerate(kept_rows)}
    source = dict(schema='refined_cap_nine_factor_body_v1', domain='unrestricted integers',
                  variant='refined_signed_cap_fused_nine_factor_source_only',
                  polynomial='sum of squares of all residuals',
                  variables=copy.deepcopy(body['variables']), residuals=copy.deepcopy(body['residuals']),
                  parent_source_manifest_sha256=PARENT_SEAL, ordinary_manifest_sha256=ORDINARY_SEAL)
    guarded = copy.deepcopy(source)
    guarded['variables'] = [copy.deepcopy(old['variables'][i]) for i in kept_vars]
    guarded['residuals'] = []
    for i in kept_rows:
        row = copy.deepcopy(old['residuals'][i])
        row['terms'] = terms(moved(poly(row['terms']), vm))
        guarded['residuals'].append(row)
    auxiliary = list(range(len(kept_vars), len(kept_vars) + 3))
    mixed = dict(kind='strict_fused_index_endpoint_product',
                 expression=[[-1, []], [1, [11, 405]], [1, [405]]],
                 existing_partial_product_coordinate=405,
                 factors=[dict(coordinate=i, shift=1) for i in [11] + list(range(16, 24))],
                 auxiliary=auxiliary, row=len(kept_rows))
    guarded['variables'] += [dict(name='nine_factor_positive.' + s, kind='integer_guard') for s in ['a', 'b', 'c']]
    guarded['residuals'].append(dict(label='domain_guard.nine_factor_positive',
                                    terms=terms(graph(poly(mixed['expression']), auxiliary))))
    kept, removed = [], []
    for spec in domain['guards']:
        if spec['row'] in DROP_ROWS:
            removed.append(copy.deepcopy(spec))
            continue
        new = copy.deepcopy(spec)
        new.update(row=rm[spec['row']], auxiliary=[vm[i] for i in spec['auxiliary']],
                   expression=terms(moved(poly(spec['expression']), vm)))
        if 'coordinate' in new:
            new['coordinate'] = vm[new['coordinate']]
        if 'pair' in new:
            new['pair'] = [vm[i] for i in new['pair']]
        kept.append(new)
    kept.append(mixed)
    occurrences = {str(v): [i for i, r in enumerate(old['residuals']) if any(v in m for c, m in r['terms'])]
                   for v in sorted(DROP_AUX)}
    plan = dict(schema='fused_nine_factor_literal_source_map_v1', parent_manifest_sha256=PARENT_SEAL,
                ordinary_manifest_sha256=ORDINARY_SEAL, old_body_to_new=[[i, i] for i in range(406)],
                old_guarded_to_new=[[i, vm[i]] for i in kept_vars],
                old_row_to_new=[dict(old_row=i, new_row=rm.get(i), status='replaced_old_graph' if i in DROP_ROWS else 'identical')
                                for i in range(len(old['residuals']))],
                removed_parent_graphs=removed, removed_private_coordinates=sorted(DROP_AUX),
                complete_removed_private_occurrences=occurrences,
                retained_parent_graphs=copy.deepcopy(interface['retained_parent_graphs']), new_fused_graph=mixed,
                all15_signed_targets=copy.deepcopy(interface['all15_signed_targets']),
                all18_actual_power_requests=copy.deepcopy(interface['all18_actual_power_requests']),
                all37_frame_atoms=copy.deepcopy(interface['all37_frame_atoms']),
                helper_reflection=copy.deepcopy(interface['helper_reflection']), chronology=copy.deepcopy(interface['chronology']),
                whole_parent_body_pointwise_fixed=True, h_and_signed_A_C_fixed=True,
                other_retained_witness_values_preserved=True, helper_normalization_only_temporary=True,
                BOTH_old_graph_triples_freshly_rechosen=True, new_triple_reused_as_old_strict_triple=False,
                sign_or_power_premise_for_N_or_K_used=False, extra_product_gate_added=False,
                optimizer_projection_or_quartic_executed=False, projected_frontier_claim=False)
    artifacts = {'source.json': source, 'guarded.json': guarded,
                 'domain.json': dict(schema='fused_nine_factor_guard_domain_v1', guards=kept), 'TRANSFORM.json': plan}
    artifacts['CALIBRATION_BINDING.json'] = dict(
        schema='fused_nine_factor_complete_source_calibration_v1', parent_manifest_sha256=PARENT_SEAL,
        ordinary_manifest_sha256=ORDINARY_SEAL, parent_calibration_sha256=digest(PARENT / 'CALIBRATION_BINDING.json'),
        source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
        generated_source_files={n: hashlib.sha256(encoded(v)).hexdigest() for n, v in artifacts.items()},
        formal_native_contracts=read(PARENT / 'CALIBRATION_BINDING.json')['formal_native_contracts'],
        witness_maps=copy.deepcopy(interface['witness_maps']),
        calibration_order=['signed_cap_t_bootstrap', 'positive_Qy_and_Qx_anchors', 'successor_factor_signs',
                           'strict_mixed_product', 'restore_BOTH_old_triples_on_original_body', 'complete_parent_calibration'],
        whole_parent_body_pointwise_fixed=True, other_retained_witness_values_preserved=True,
        complete_parent_guarded_tuple_restored_before_calibration=True,
        new_unbounded_or_Lean_theorem_claimed=False, optimizer_projection_or_quartic_executed=False)
    return artifacts, body, old, vm, rm

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
    need(set(artifacts) == set(exp), 'complete five-artifact namespace')
    for name, value in exp.items():
        need(artifacts[name] == value, 'whole independently reconstructed artifact ' + name)
    source, guarded, domain, plan = [artifacts[n] for n in NAMES[:4]]
    need(source['variables'] == body['variables'] and source['residuals'] == body['residuals'], 'all406 body coordinates and all341 rows fixed')
    need(source['domain'] == guarded['domain'] == 'unrestricted integers', 'whole unrestricted domain')
    need(len(guarded['variables']) == 475 and len(guarded['residuals']) == 364 and len(domain['guards']) == 24, 'exact declared source namespace')
    need(len({v['name'] for v in guarded['variables']}) == len(guarded['variables']), 'fresh unique names')
    for row in guarded['residuals']:
        need(row['terms'] == terms(poly(row['terms'])), 'complete canonical coefficient list')
        need(all(type(c) is int and len(m) <= 2 and all(type(i) is int and 0 <= i < 475 for i in m)
                 for c, m in row['terms']), 'integer quadratic residuals')
    need({i for r in guarded['residuals'] for c, m in r['terms'] for i in m} == set(range(475)), 'all declared coordinates occur')
    need(set(vm) == set(range(478)) - DROP_AUX and set(vm.values()) == set(range(472)), 'entire retained old coordinate bijection')
    need(set(rm) == set(range(365)) - DROP_ROWS and set(rm.values()) == set(range(363)), 'entire retained old row bijection')
    for i, j in vm.items():
        need(old['variables'][i] == guarded['variables'][j], 'every retained old coordinate metadata')
    for i, j in rm.items():
        row = copy.deepcopy(old['residuals'][i]); row['terms'] = terms(moved(poly(row['terms']), vm))
        need(row == guarded['residuals'][j], 'every complete retained old residual')
    interface = read(ORDINARY / 'INTERFACE.json')
    need(plan['removed_parent_graphs'] == interface['removed_parent_graphs'] and
         plan['retained_parent_graphs'] == interface['retained_parent_graphs'], 'complete25 old guard partition')
    for spec in plan['removed_parent_graphs']:
        need(old['residuals'][spec['row']] == interface['removed_complete_parent_graph_rows'][str(spec['row'])], 'both whole removed graph rows')
        for v in spec['auxiliary']:
            need([i for i, r in enumerate(old['residuals']) if any(v in m for c, m in r['terms'])] == [spec['row']], 'all six old witnesses private')
    for spec in domain['guards']:
        need(poly(guarded['residuals'][spec['row']]['terms']) == graph(poly(spec['expression']), spec['auxiliary']), 'every complete retained/new Legendre graph')
        for v in spec['auxiliary']:
            need([i for i, r in enumerate(guarded['residuals']) if any(v in m for c, m in r['terms'])] == [spec['row']], 'all retained and fresh graph witnesses private')
    mixed = plan['new_fused_graph']
    need(mixed['auxiliary'] == [472, 473, 474] and mixed['row'] == 363, 'fresh mixed graph namespace')
    need(guarded['residuals'][363] == interface['declared_new_graph_row'], 'every actual mixed-row coefficient')
    need(plan['old_guarded_to_new'] == interface['declared_retained_old_coordinate_to_new'] and
         [[i, j] for i, j in sorted(rm.items())] == interface['declared_retained_old_row_to_new'], 'whole ordinary witness maps')
    restoration = {}
    for offset in range(7):
        v = 399 + offset; p = poly(source['residuals'][334 + offset]['terms'])
        need(p.pop((v,), 0) == 1 and not any(v in m for m in p), 'all seven unchanged product definitions monic')
        q = scale(p, -1)
        for earlier, value in restoration.items():
            q = substitute(q, earlier, value)
        restoration[v] = q
    product = C(1)
    for i in range(16, 24):
        product = mul(product, add(V(i), C(1)))
    need(restoration[405] == product, 'whole unchanged eight-factor polynomial')
    need(substitute(poly(mixed['expression']), 405, product) == add(mul(add(V(11), C(1)), product), C(-1)), 'whole fused nine-factor polynomial')
    for i, row in interface['literal_parent_rows'].items():
        need(source['residuals'][int(i)] == row, 'all181 ordinary whole literal rows')
    for cut in interface['all11_successor_source_ideal_identities']:
        p = add(*[mul(poly(t['multiplier']), poly(source['residuals'][t['row']]['terms'])) for t in cut['source_ideal_combination']])
        need(p == poly(cut['identity_residual']), 'all eleven whole successor source ideals')
    cuts = interface['bootstrap_source_row_cuts']
    p = add(*[scale(poly(source['residuals'][q['row']]['terms']), q['multiplier']) for q in cuts['ceiling']['combination']])
    need(p == poly(cuts['ceiling']['identity_terms']), 'whole t-only ceiling source cut')
    for name in ['Qy_positive_anchor', 'Qx_positive_anchor']:
        cut = cuts[name]
        need(poly(source['residuals'][cut['row']]['terms']) == poly(cut['identity_terms']), 'actual positive output anchor ' + name)
        need(all(any(g.get('coordinate') == v and g['kind'] == 'nonnegative' for g in domain['guards'])
                 for v in cut['retained_scalar_coordinates']), 'every anchor scalar graph retained')
    atoms = plan['all37_frame_atoms']
    need(poly(source['residuals'][333]['terms']) == add(V(245), C(-4), *[scale(mul(poly(a['affine']), poly(a['affine'])), -2) for a in atoms]), 'complete37-atom absolute frame')
    for request in plan['all18_actual_power_requests']:
        for role in ['base', 'exponent', 'output']:
            need(any(poly(request['ports'][role]) == poly(a['affine']) for a in atoms), 'all54 actual bounded ports')
    macros = macro_bindings(source, plan['all18_actual_power_requests'], plan['all15_signed_targets'])
    reflection = {int(i): poly(p) for i, p in plan['helper_reflection'].items()}
    def reflect(p):
        for i, value in reflection.items():
            p = substitute(p, i, value)
        return p
    for i in range(475):
        need(reflect(reflect(V(i))) == V(i), 'whole helper coordinate involution')
    for i, row in enumerate(guarded['residuals']):
        need(reflect(poly(row['terms'])) == scale(poly(row['terms']), -1 if i in [205, 322] else 1), 'all364 complete helper row identities')
    need(all(reflect(V(i)) == V(i) for i in [11, 395, 405] + list(range(16, 25))), 'recovered scalars, h and product fixed by temporary reflection')
    # Diagnostic only: the new triple need not represent either old value.
    value = lambda a, b, c: a*a + b*b + c*(c+1)
    need(value(2, 2, 0) == (2+1)*3-1 and value(2, 2, 0) != 2 and value(1, 1, 0) == 2, 'fresh BOTH-old-triple distinction')
    # Arbitrary signed fixtures compare identities; no source-zero claim.
    for phase in [2, 7]:
        values = [((i + phase) % 13 - 6) * (-1 if i % 2 else 1) for i in range(475)]
        previous = [0] * 478
        for i, j in vm.items():
            previous[i] = values[j]
        def evaluate(p, vector):
            result = 0
            for m, c in p.items():
                term = c
                for i in m:
                    term *= vector[i]
                result += term
            return result
        for i, j in rm.items():
            need(evaluate(poly(old['residuals'][i]['terms']), previous) == evaluate(poly(guarded['residuals'][j]['terms']), values), 'all363 signed retained-row fixtures')
    return dict(whole406_body_and341_rows=True, whole25_parent_graph_partition=True,
                all_coordinate_and_row_bijections=True, all_private_graph_witnesses=True,
                whole_eight_and_nine_factor_polynomials=True, all181_literal_rows=True,
                all11_source_ideals_and_three_bootstrap_cuts=True, all37_frame_atoms_and54_ports=True,
                actual_power_interfaces=macros, full475_coordinate_and364_row_reflection=True,
                both_old_triples_require_fresh_rechoice=True, signed_retained_row_fixtures=2,
                complete_calibration=artifacts['CALIBRATION_BINDING.json'], source_only=True,
                projected_frontier_claim=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, default=HERE)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); pins = authenticate()
    artifacts = {n: read(args.packet / n) for n in NAMES}
    for name, value in artifacts.items():
        need((args.packet / name).read_bytes() == encoded(value), 'whole canonical artifact ' + name)
    evidence = validate(artifacts); rejected = []
    def trial(label, change):
        altered = copy.deepcopy(artifacts); change(altered)
        try:
            validate(altered)
        except (ValueError, KeyError, TypeError, IndexError, StopIteration):
            rejected.append(label)
        else:
            raise ValueError('actual artifact corruption accepted ' + label)
    for i in [0, 1, 3, 7, 184, 191, 205, 217, 218, 226, 253, 266, 291, 306, 322, 333, 334, 340]:
        trial('actual body residual ' + str(i), lambda d, i=i: d['source.json']['residuals'][i]['terms'][0].__setitem__(0, 999))
    trial('whole body metadata', lambda d: d['source.json']['variables'][11].__setitem__('name', 'changed'))
    trial('integer domain', lambda d: d['guarded.json'].__setitem__('domain', 'nonnegative integers'))
    trial('retained witness metadata', lambda d: d['guarded.json']['variables'][406].__setitem__('name', 'changed'))
    trial('mixed nonlinear coefficient', lambda d: d['guarded.json']['residuals'][-1]['terms'][1].__setitem__(0, 2))
    trial('mixed constant threshold', lambda d: d['domain.json']['guards'][-1]['expression'][0].__setitem__(0, 0))
    trial('missing ninth factor', lambda d: d['domain.json']['guards'][-1]['factors'].pop(0))
    trial('new witness escape', lambda d: d['guarded.json']['residuals'][0]['terms'].append([1, [472]]))
    trial('missing old coordinate map', lambda d: d['TRANSFORM.json']['old_guarded_to_new'].pop())
    trial('wrong old graph row map', lambda d: d['TRANSFORM.json']['old_row_to_new'][344].__setitem__('new_row', 344))
    trial('missing old removed witness', lambda d: d['TRANSFORM.json']['removed_private_coordinates'].pop())
    trial('wrong actual call11 row', lambda d: d['TRANSFORM.json']['all18_actual_power_requests'][11].__setitem__('row', 296))
    trial('wrong actual call14 row', lambda d: d['TRANSFORM.json']['all18_actual_power_requests'][14].__setitem__('row', 311))
    trial('wrong actual call label', lambda d: d['TRANSFORM.json']['all18_actual_power_requests'][14].__setitem__('label', 'pow15.power_congruence'))
    trial('wrong actual port', lambda d: d['TRANSFORM.json']['all18_actual_power_requests'][14]['ports']['output'][0][1].__setitem__(0, 229))
    trial('new auxiliary in frame', lambda d: d['TRANSFORM.json']['all37_frame_atoms'][0]['affine'].append([1, [472]]))
    for key, value in [('whole_parent_body_pointwise_fixed', False), ('h_and_signed_A_C_fixed', False),
                       ('other_retained_witness_values_preserved', False), ('helper_normalization_only_temporary', False),
                       ('BOTH_old_graph_triples_freshly_rechosen', False), ('new_triple_reused_as_old_strict_triple', True),
                       ('sign_or_power_premise_for_N_or_K_used', True), ('extra_product_gate_added', True)]:
        trial('wrong ordinary boundary ' + key, lambda d, key=key, value=value: d['TRANSFORM.json'].__setitem__(key, value))
    trial('wrong chronology', lambda d: d['TRANSFORM.json']['chronology'].reverse())
    trial('wrong ordinary seal', lambda d: d['CALIBRATION_BINDING.json'].__setitem__('ordinary_manifest_sha256', '0' * 64))
    trial('missing generated source binding', lambda d: d['CALIBRATION_BINDING.json']['generated_source_files'].pop('guarded.json'))
    trial('calibration before both old triples', lambda d: d['CALIBRATION_BINDING.json']['calibration_order'].reverse())
    trial('missing artifact', lambda d: d.pop('domain.json'))
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), source_only=True,
                  evidence=evidence, actual_corruptions_rejected=rejected,
                  source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
                  generated={n: digest(args.packet / n) for n in NAMES})
    target = args.output.resolve()
    need(not any(target.is_relative_to((ROOT / n).resolve()) for n in pins['closed_dependencies']), 'never write a closed dependency')
    need(not (HERE / 'MANIFEST.json').exists() or not target.is_relative_to(HERE), 'receipt outside sealed packet')
    data = encoded(result)
    need(not args.output.is_symlink() and (not args.output.exists() or args.output.read_bytes() == data), 'refuse changed receipt')
    args.output.parent.mkdir(parents=True, exist_ok=True); args.output.write_bytes(data)
    print(data.decode(), end='')


if __name__ == '__main__':
    main()


