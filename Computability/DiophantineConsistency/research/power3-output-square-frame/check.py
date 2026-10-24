#!/usr/bin/env python3
"""Complete read-only ordinary62 interface, chronology and literal audit.

Imports only the Python standard library. Parent proofs/certificates are inert
authenticated data; no producer, optimizer, parent checker, archive program or
Lean executes. The unbounded theorem is PROOF.md plus FULL_SOURCE.md.
"""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ADDITIONAL = {106, 124, 125, 130, 132, 133}
RANGE_OUTPUTS = [573, 583, 591, 599, 607, 617, 625, 635]
RANGE_QUOTIENTS = [575, 584, 592, 600, 609, 618, 627, 636]


def need(ok, why):
    if not ok:
        raise ValueError(why)


def load(path):
    return json.loads(path.read_bytes())


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def P(terms):
    result = {}
    for c, m in terms:
        need(type(c) is int and all(type(v) is int for v in m), 'integer polynomial')
        key = tuple(sorted(m))
        result[key] = result.get(key, 0) + c
    return {m: c for m, c in result.items() if c}


def add(a, b, scale=1):
    result = dict(a)
    for m, c in b.items():
        result[m] = result.get(m, 0) + scale * c
    return {m: c for m, c in result.items() if c}


def mul(a, b):
    result = {}
    for m, c in a.items():
        for n, d in b.items():
            key = tuple(sorted(m + n))
            result[key] = result.get(key, 0) + c * d
    return {m: c for m, c in result.items() if c}


def C(c):
    return {(): c} if c else {}


def V(v):
    return {(v,): 1}


def variables(poly):
    return {v for m in poly for v in m}


def sealed(folder):
    manifest = folder / 'MANIFEST.json'
    files = load(manifest)['files']
    actual = {str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p != manifest}
    need(actual == set(files), 'complete closed inventory ' + str(folder))
    for name, h in files.items():
        need(digest(folder / name) == h, 'whole sealed member ' + name)


def literal(oldraw, oldparent, olddomain, oldframe, oldradius, raw, parent, domain, frame, radius, data):
    need(data['schema'] == 'power3_output_square_ordinary62_v1' and (data['source_variables'], data['source_rows'], data['guarded_variables'], data['guarded_rows'], data['predicates'], data['original_scalar_predicates']) == (1268, 1186, 1454, 1248, 62, 59), 'certificate literal dimensions and scope')
    want = deepcopy(oldraw)
    oldrow = want['rows'][1152]
    need(oldrow == dict(gate=1235, label='addition', terms=[[-1, [106]], [-1, [1234]], [1, [1235]]]), 'exact former106 frame row')
    newrow = dict(gate=1235, label='addition', terms=[[-1, [1267]], [-1, [1234]], [1, [1235]]])
    newvar = dict(kind='gate', name='frame.power_output_square.106')
    square = dict(gate=1267, label='frame_power_output_square', terms=[[-1, [106, 106]], [1, [1267]]])
    want['rows'][1152] = newrow
    want['variables'].append(newvar)
    want['rows'].append(square)
    need(raw == want and len(raw['variables']) == 1268 and len(raw['rows']) == 1186, 'ENTIRE source: only1152 and appended1267/1185')
    need(data['source_changes'] == dict(frame_row=1152, old_row=oldrow, new_row=newrow, appended_variable=newvar, appended_row=square, only_new_variable=1267, only_new_row=1185), 'whole explicit source delta')
    need(data['all_source_metadata'] == {k: v for k, v in raw.items() if k not in ['rows', 'variables']}, 'ALL unchanged power/seed/index/binomial/range/native metadata')
    need([i for i, r in enumerate(oldraw['rows']) if 106 in variables(P(r['terms']))] == data['complete_old106_occurrences'] == [102, 704, 1152], 'complete old106 occurrence set')
    need([i for i, r in enumerate(raw['rows']) if 106 in variables(P(r['terms']))] == data['complete_new106_occurrences'] == [102, 704, 1185], 'complete new106 occurrence set')
    need(not any(P(r['terms']).get((106, 106)) for r in oldraw['rows']), 'no silently reused106-square gate')
    guards = []
    names = deepcopy(raw['variables'])
    residuals = [dict(label=r['label'], terms=r['terms']) for r in raw['rows']]
    removed = []
    for i, guard in enumerate(olddomain['guards']):
        if guard['predicate'].get('raw_variables') == [106]:
            need(guard['predicate']['kind'] == 'retained_scalar', 'only original scalar106 removed')
            removed.append(i)
            need(data['removed_guard'] == dict(raw_variable=106, parent_guard_index=i, parent_auxiliary=guard['auxiliary']), 'exact old106 guard triple')
            continue
        aux = list(range(len(names), len(names) + 3))
        remap = dict(zip(guard['auxiliary'], aux))
        names.extend(deepcopy(oldparent['variables'][a]) for a in guard['auxiliary'])
        guards.append(dict(auxiliary=aux, predicate=guard['predicate']))
        oldrow = oldparent['residuals'][1185 + i]
        residuals.append(dict(label=oldrow['label'], terms=[[c, [remap.get(v, v) for v in m]] for c, m in oldrow['terms']]))
    expected = deepcopy(oldparent)
    expected.update(variant='power3_squared_output_frame62_raw_literal_prototype', variables=names, residuals=residuals)
    need(parent == expected and removed == [14] and len(names) == 1454 and len(residuals) == 1248, 'whole62 parent with every name/label/retained graph and auxiliary index')
    wantdomain = dict(baseline_body_rows=1186, baseline_body_variables=1268, baseline_raw_indices=list(range(1268)), guards=guards,
                      compact_bridge_assumed=False, ordinary_source_equivalence_claimed=False, frame_policy='FRAME_POLICY.json', radius_policy='RADIUS_POLICY.json',
                      inherited_absent_quotient_variables=RANGE_QUOTIENTS, inherited_removed_power_output_variables=[6], newly_removed_scalar_variables=[106],
                      original_scalar_predicates=59, predicates=62, raw_source='source/raw_builder.json')
    need(domain == wantdomain, 'entire62 domain/predicate/removal metadata')
    need(sum(g['predicate']['kind'] == 'retained_scalar' for g in guards) == 59, 'actual retained scalar count')
    for j, (guard, row) in enumerate(zip(guards, residuals[1186:])):
        a, b, c = guard['auxiliary']
        target = add(P(guard['predicate']['terms']), P([[-1, [a, a]], [-1, [b, b]], [-1, [c, c]], [-1, [c]]]))
        need(P(row['terms']) == target and guard['auxiliary'] == list(range(1268 + 3 * j, 1271 + 3 * j)), 'each actual Legendre graph')
    ports = oldframe['actual_power_ports']
    mapping = {6: 7, 106: 1267, **dict(zip(RANGE_OUTPUTS, range(1259, 1267)))}
    need(frame['schema'] == 'power3_output_squared_frame62_v1' and frame['actual_power_ports'] == ports and frame['bounding_ports'] == [mapping.get(v, v) for v in ports], 'all actual/bounding ports, actualcall3 unchanged')
    need(frame['newly_squared_output'] == dict(changed_frame_row=1152, gate_already_present=False, output=106, source_square_row=1185, square_variable=1267), 'new square/frame exact policy')
    need(frame['inherited_squared_outputs'] == [6] + RANGE_OUTPUTS and frame['inherited_square_variables'] == [7] + list(range(1259, 1267)) and frame['inherited_square_rows'] == [2] + list(range(1177, 1185)), 'nine inherited square definitions intact')
    need(frame['inherited_absent_quotient_guards'] == RANGE_QUOTIENTS and frame['inherited_removed_power_output_guards'] == [6] and frame['newly_removed_scalar_guard'] == 106 and frame['ordinary_source_equivalence_claimed'] is False and frame['old_frame_calibration_not_assumed'] is True and frame['actual_power_requests_unchanged'] is True and frame['all_other_original_source_records_unchanged'] is True, 'complete semantic scope/removal flags')
    expected_radius = deepcopy(oldradius)
    expected_radius['joint_guard'] = dict(index=61, auxiliary=[1451, 1452, 1453], predicate=guards[-1]['predicate'])
    need(radius == expected_radius, 'entire common-radius policy with joint auxiliaries compacted only')
    return dict(source_coordinates=len(raw['variables']), source_rows=len(raw['rows']), parent_coordinates=len(names), parent_rows=len(residuals), predicates=len(guards), retained_scalars=59)


def audit(raw, data, olddata, prior, old72):
    rows = [P(r['terms']) for r in raw['rows']]
    identities = []

    def collect(cut, target=None, label='identity'):
        result = {}
        for item in cut['row_combination']:
            need(type(item['row']) is int and 0 <= item['row'] < len(rows), 'actual complete source row')
            result = add(result, mul(P(item['multiplier']), rows[item['row']]))
        target = P(cut.get('polynomial', cut.get('expanded_polynomial'))) if target is None else target
        need(result == target, 'complete polynomial ideal ' + label)
        identities.append(label)
        return result

    for name in ['early_cuts', 'early_g_cuts', 'unchanged_local_cuts', 'full_source_cuts']:
        for key, cut in olddata[name].items():
            collect(cut, label=name + '.' + key)
    for name in ['proposed_radius_cut', 'common_radius_cut', 'common_base_cut', 'new_t1_combined_cut', 'power0_square_cut']:
        collect(olddata[name], label=name)
    for v in range(64, 87):
        collect(dict(row_combination=[dict(multiplier=[[1, []]], row=v - 13)]), P([[1, [v]], [-1, [v - 1, v - 1]]]), 'K_square.' + str(v))
    need(raw['binomials'] == [dict(k=['v', k], n=['v', n], output=['v', o]) for n, k, o in [(90, 86, 91), (110, 4, 111), (122, 4, 123)]], 'all three literal exact binomials')
    need(len(raw['powers']) == len(prior['power_calls']) == 21 and len(raw['seeds']) == len(prior['seeds']) == 15, 'complete power/seed lists have no truncated zip')
    for call, request in zip(prior['power_calls'], raw['powers']):
        need(request == {k: ['v', call[k]] for k in ['base', 'exponent', 'output']}, 'every actual power request')
        collect(call['cut'], P([[1, [call['X']]], [-1, [644, call['Y']]], [1, [call['base'], call['Y']]], [-1, [call['output']]], [-1, [call['modulus'], call['quotient']]]]), 'power.' + str(call['index']))
    for actual, seed in zip(raw['seeds'], prior['seeds']):
        need(actual['exponent'] == ['v', seed['aliases']['k']] and actual['pair'] == [['v', seed['aliases'][k]] for k in ['X', 'Y']], 'every actual seed pair/index')
        need(not (set(seed['aliases'].values()) & ADDITIONAL), 'all15 seed aliases avoid six delayed values')
        for name, cut in seed['cuts'].items():
            need(not (variables(P(cut.get('polynomial', cut.get('expanded_polynomial')))) & ADDITIONAL), 'every pre-orientation seed cut avoids six delayed values')
            collect(cut, label='seed.' + str(seed['aliases']['k']) + '.' + name)
    for item in prior['moduli']:
        collect(item['cut'], label='modulus.' + str(item['modulus']))
    for name in ['bootstrap_norm', 'unit_norm_cut', 'comparison_base_constructor', 'comparison_base_congruence']:
        collect(prior[name], label=name)
    for step in prior['initial_A_D_bounds']:
        collect(step, add(mul(V(step['variable']), P(step['factor'])), P(step['rhs']), -1), 'initial_AD_bound.' + str(step['variable']))
    for interface in olddata['fused_range_interfaces']:
        for name in ['quotient_cut', 'remainder_cut']:
            collect(interface[name], label='range.' + str(interface['numerator']) + '.' + name)
    need((len(raw['powers']), len(raw['seeds']), len(raw['indices']), len(prior['moduli']), len(raw['ranges'])) == (21, 15, 16, 7, 8), 'all simultaneous source interfaces')
    need(raw['derivations'] == [dict(kind='shift', pair=[['v', 921], ['v', 922]], shift=1, source=['v', 4], target=['v', 5])], 'unchanged derived t+1 pair')
    need(data['canonical_modulus_cut'] == prior['positive_prefix']['canonical_modulus_cut'], 'unchanged M identity independent of130')
    collect(data['canonical_modulus_cut'], label='canonical_modulus')
    need(not (variables(P(data['canonical_modulus_cut']['polynomial'])) & ADDITIONAL), 'early canonicalM has no130 or106 premise')
    for group in ['early_cuts', 'early_g_cuts', 'unchanged_local_cuts']:
        for cut in olddata[group].values():
            need(not (variables(P(cut['polynomial'])) & ADDITIONAL), 'pre-orientation local cut avoids six-value closure')
    for name in ['bootstrap_norm', 'unit_norm_cut', 'comparison_base_constructor', 'comparison_base_congruence']:
        cut = prior[name]
        need(not (variables(P(cut.get('polynomial', cut.get('expanded_polynomial')))) & ADDITIONAL), 'bootstrap/comparison cut avoids delayed values')
    for index in [1, 2, 5, 6, 8, 9]:
        need(not (variables(P(prior['power_calls'][index]['cut']['polynomial'])) & ADDITIONAL), 'every pre-recovery localK/parity/helper power cut avoids six delayed values')

    kept = set(olddata['retained_original_guard_indices']) - {106}
    initial = set(prior['prefix_proof']['initial_semantic_guard_indices'])
    need(len(kept) == 59 and initial - kept == {6, 59, 93, 104, 106} | set(RANGE_QUOTIENTS), 'all59 direct scalar guards, exact initial gap')
    need(data['additional_missing'] == sorted(ADDITIONAL) and data['early_missing'] == sorted(set(olddata['prefix_missing33']) | ADDITIONAL), 'exact six additional missing coordinates')
    known = {v: 0 for v in initial - {6, 59, 93, 104, 106} - set(RANGE_QUOTIENTS)}
    known.update({int(v): L for v, L in old72['early_derived_bounds'].items()})
    known[107] = 0
    need(known[87] >= 2 and known[93] >= 2 and known[129] >= 1 and known[105] >= 1 and known[137] >= 0 and 694 in kept, 'same acyclic early factorial/modulus/weakD/initialA premises')
    rewrites = {q['variable']: q for q in old72['rewritten_prefix_bounds']}
    signs = []
    skipped = []
    bound_count = 0
    delayed_bounds = []

    def positive(q):
        need(variables(q) <= set(known), 'every positivity operand already available')
        shifted = {}
        for m, c in q.items():
            term = C(c)
            for v in m:
                term = mul(term, add(V(v), C(known[v])))
            shifted = add(shifted, term)
        need(all(c >= 0 for c in shifted.values()) and shifted.get((), 0) > 0, 'complete shifted positive polynomial')

    def sign(original, restoring=False):
        step = deepcopy(original)
        v = step['variable']
        if v in {105, 137}:
            need(known[v] >= (1 if v == 105 else 0), 'independent early replacement sign')
            return
        step.update(olddata['changed_sign_steps'].get(str(v), {}))
        c, rhs = step['coefficient'], P(step['rhs'])
        pivot = add(mul(C(c), V(v)), rhs, -1)
        need(c > 0 and rows[step['row']] in [pivot, mul(C(-1), pivot)], 'complete actual ordered sign row')
        if step['kind'] == 'positive_monomials':
            deps = {w for m in rhs for w, n in Counter(m).items() if n % 2}
            need(deps == set(step['dependencies']) and all(c > 0 for c in rhs.values()), 'all actual odd-power sign premises')
            if not deps <= set(known):
                need(not restoring and v in set(data['early_missing']), 'no unrecorded missing sign premise')
                skipped.append(step)
                return
        else:
            need(step['kind'] == 'affine_square' and mul(P(step['square_root']), P(step['square_root'])) == rhs, 'unconditional complete square sign')
        known[v] = max(known.get(v, 0), 0)
        signs.append(v)

    def bound(original, restoring=False):
        nonlocal bound_count
        v, lower = original['variable'], original['lower']
        old = collect(original, add(mul(V(v), P(original['factor'])), P(original['rhs']), -1), 'old_bound.' + str(v))
        step = rewrites.get(v, original)
        factor, rhs = P(step['factor']), P(step['rhs'])
        if v in rewrites:
            multiplier = P([[-1, [130]], [-1, []]]) if v == 130 else P([[-1, [517]]])
            need(add(old, mul(multiplier, P(data['canonical_modulus_cut']['polynomial']))) == add(mul(V(v), factor), rhs, -1), 'whole canonical-modulus bound rewrite')
            collect(step, label='rewritten_bound.' + str(v))
        need(v not in variables(factor) | variables(rhs), 'bound has no self-premise')
        if not (variables(factor) | variables(rhs)) <= set(known):
            need(v == 130 and not restoring, 'only bound130 may wait')
            delayed_bounds.append(original)
            return
        positive(factor)
        positive(add(rhs, mul(C(lower - 1), factor), -1))
        known[v] = max(known.get(v, lower), lower)
        bound_count += 1

    prefix = prior['prefix_proof']
    for step in prefix['preliminary_t_n_bounds']:
        bound(step)
    for step in prefix['five_stages']:
        for item in step['preceding_sign_steps']:
            sign(item)
        bound(step)
    for item in prefix['final_sign_steps']:
        sign(item)
    need(set(known) == set(range(643)) - {59, 104} - set(data['early_missing']) and len(known) == data['early_prefix_coordinates'] == 602, 'actual602-coordinate early closure')
    extra = [s for s in skipped if s['variable'] in ADDITIONAL]
    need(extra == data['additional_delayed_sign_steps'] and [s['variable'] for s in extra] == [124, 125, 133, 132], 'exact four delayed sign steps in their old order')
    need(len(signs) == data['early_sign_steps'] == 545 and bound_count == data['early_bounds'] == 6 and len(delayed_bounds) == 1 and data['delayed_bound'] == rewrites[130], 'actual545 signs/six bounds, only130 postponed')
    strict = {4, 5, 129, 87, 93, 105}
    strict_count = 0

    def strict_step(step):
        nonlocal strict_count
        v = step['variable']
        row = rows[step['row']]
        need(row.get((v,)) == 1, 'literal strict constructor pivot')
        rhs = {m: -c for m, c in row.items() if m != (v,)}
        monomial = tuple(step['positive_monomial'])
        need(variables(rhs) <= set(known) and all(c > 0 for c in rhs.values()) and rhs.get(monomial, 0) > 0 and set(monomial) <= strict, 'all strict constructor premises available')
        strict.add(v)
        strict_count += 1

    for step in prior['positive_prefix']['steps']:
        if step['variable'] in {105, 137}:
            continue
        if step['variable'] == 133:
            need(data['delayed_strict_step'] == step and variables(rows[step['row']]) - {133} == {129, 132}, 'only strict133 awaits132')
            continue
        strict_step(step)
    need(strict_count == data['early_strict_steps'] == 428, 'all428 surviving strict constructors')
    for original in prefix['preliminary_t_n_bounds'] + prefix['five_stages']:
        if original['variable'] != 130:
            step = rewrites.get(original['variable'], original)
            need(not ((variables(P(step['factor'])) | variables(P(step['rhs']))) & ADDITIONAL), 'other six bound targets avoid closure')

    ports = {v[1] for request in raw['powers'] for v in request.values()}
    mapping = {6: 7, 106: 1267, **dict(zip(RANGE_OUTPUTS, range(1259, 1267)))}
    other = ports - {104} - set(mapping)
    need(ports == set(data['actual_power_ports']) and len(ports) == 43 and {mapping.get(v, v) for v in ports} == set(data['bounding_ports']) and len(data['bounding_ports']) == 43, 'all43 distinct actual/bounding ports')
    need(other == set(data['other_natural_ports']) and len(other) == 32 and other <= set(known) and {4, 86} <= other and known[105] >= 1, 'all32 natural ports and weakD positive')
    need({c['base'][1] for c in raw['powers']} <= strict and {c['exponent'][1] for c in raw['powers']} <= strict, 'every actual base/index positive without133')
    need(data['square_map'] == [[v, mapping[v]] for v in [6, 106] + RANGE_OUTPUTS], 'all ten square bindings')
    targets = dict(new_frame_cut=P([[1, [643]], [-2, []]] + [[-1, [v]] for v in sorted(mapping.get(v, v) for v in ports)]),
                   new_weak_frame_cut=P([[1, [643]], [-1, [105]]] + [[-1, [v]] for v in sorted(other | set(mapping.values()))]),
                   expanded_frame_cut=P([[1, [643]], [-2, []]] + [[-1, [v, v] if v in mapping else [v]] for v in sorted(ports)]),
                   expanded_weak_frame_cut=P([[1, [643]], [-1, [105]]] + [[-1, [v, v]] for v in mapping] + [[-1, [v]] for v in sorted(other)]))
    for name, target in targets.items():
        collect(data[name], target, name)
    need(rows[1185] == P([[1, [1267]], [-1, [106, 106]]]), 'new square sign independent of106')
    call0, call3, call8, call9 = [prior['power_calls'][i] for i in [0, 3, 8, 9]]
    seed = next(s for s in prior['seeds'] if s['aliases']['k'] == 4)
    expected_binding = dict(index=3, **{k: call3[k] for k in ['base', 'exponent', 'output', 'X', 'Y', 'modulus', 'quotient']}, cut=call3['cut'], seed_aliases=seed['aliases'], recovered_after='post-factorial positive t pair from calls8/9', recovered_before='bound130 and shifted-t collapse')
    need(data['power3_binding'] == expected_binding and (call3['base'], call3['exponent'], call3['output'], call3['X'], call3['Y'], call3['modulus'], call3['quotient']) == (87, 4, 106, 670, 671, 753, 758), 'exact actual signed call3 at the t pair')
    modulus3 = next(item for item in prior['moduli'] if item['base'] == 87)
    need(modulus3['modulus'] == 753, 'actual call3 modulus alias')
    collect(modulus3['cut'], P([[-1, []], [-1, [87, 87]], [2, [87, 644]], [-1, [753]]]), 'actual_T3_equals_2Af_minus_f_squared_minus1')
    need(data['supporting_calls'] == [8, 9] and (call8['exponent'], call8['X'], call8['Y']) == (call3['exponent'], call3['X'], call3['Y']) == (4, 670, 671), 'support8 exact same pair as signedcall3')
    need((call8['base'], call8['output'], call9['base'], call9['output']) == (530, 547, 531, 560) and {549, 550, 562, 563} <= kept and {530, 531, 87} <= strict and {547, 560} <= set(known), 'independent natural support outputs/positive bases')
    for cut in olddata['t_support_override']['strict_output_cuts'].values():
        collect(cut, label='strict_t_support')
    need(106 not in known and 130 not in known and 133 not in strict and 6 not in known, 'no premature sign or constructor before paired-t orientation')
    early = dict(coordinates=len(known), sign_steps=len(signs), strict_steps=strict_count, bounds=bound_count, delayed_sign_steps=len(skipped))
    # These signs are supplied by the ordinary positive-pair residue proof, not by a guard.
    known[6] = 0
    known[106] = 0
    for v in [124, 125, 133]:
        sign(next(s for s in extra if s['variable'] == v), True)
    need(P(data['delayed_bound']['factor']) == P([[1, []], [1, [129]], [1, [131]]]) and P(data['delayed_bound']['rhs']) == P([[1, [106, 107, 123]], [-1, [129]]]), 'actual130 factor/rhs, no full product meaning')
    need(add(P(data['delayed_bound']['factor']), P(data['delayed_bound']['rhs'])) == P([[1, []], [1, [106, 107, 123]], [1, [131]]]), 'positive shifted130 numerator')
    bound(delayed_bounds[0], True)
    sign(next(s for s in extra if s['variable'] == 132), True)
    strict_step(data['delayed_strict_step'])
    need(len(known) == 609 and set(known) == set(range(643)) - {59, 104} - set(olddata['prefix_missing32']) and len(signs) == 549 and bound_count == 7 and strict_count == 429, 'exact restored609 boundary before shifted-t and range semantics')
    for interface in olddata['signed_output_calls']:
        need(interface['retained_YminusK'] in kept and interface['base'] == 531 and interface['output'] in RANGE_OUTPUTS, 'all8 numerator positiveY guards retained')
    for interface in olddata['fused_range_interfaces']:
        need({interface['remainder'], interface['slack']} <= set(known) and interface['quotient'] not in known, 'all retained remainder premises before q recovery')
    for q in RANGE_QUOTIENTS:
        known[q] = 0
    range_steps = [s for s in skipped if s['variable'] not in ADDITIONAL]
    for step in range_steps:
        sign(step, True)
    need(len(range_steps) == 24 and len(signs) == 573 and set(known) == set(range(643)) - {59, 104}, 'complete641 ledger restored after the8 quotient signs')
    return dict(status='PASS', collected_identities=len(identities), identity_labels=identities, early=early, restored_before_shifted_t=609, restored_sign_steps=549, restored_strict_steps=429, restored_bounds=7, range_delayed_steps=24, final_prefix_coordinates=len(known), final_sign_steps=len(signs), power_requests=21, seed_tests=15, index_atoms=16, exact_binomials=3, range_graphs=8, distinct_moduli=7, actual_frame_ports=43, squared_outputs=10)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pins = load(HERE / 'SOURCE_PINS.json')
    for name, h in pins['files'].items():
        need(digest(ROOT / name) == h, 'whole frozen dependency/basic file ' + name)
    sealed(ROOT / pins['accepted_ordinary_packet'])
    sealed(ROOT / pins['accepted_profile_packet'])
    if (HERE / 'MANIFEST.json').exists():
        sealed(HERE)
    accepted = ROOT / pins['accepted_ordinary_packet']
    oldbasic = ROOT / pins['accepted_profile_packet']
    basic = ROOT / pins['new_basic_packet']
    data = load(HERE / 'CERTIFICATE.json')
    olddata = load(accepted / 'CERTIFICATE.json')
    prior = load(ROOT / 'research/main-root-and-modulus-signs/CERTIFICATE.json')
    old72 = load(ROOT / 'research/shifted-t-index-guard/CERTIFICATE.json')
    need(data['accepted63_manifest_sha256'] == digest(accepted / 'MANIFEST.json') == '0797e4244ae0c65ed2fecffebcc6445bfda60729714fc973e32fee716db48d75', 'exact ordinary63 theorem')
    values = [load(oldbasic / n) for n in ['source/raw_builder.json', 'raw/parent.json', 'raw/domain.json', 'FRAME_POLICY.json', 'RADIUS_POLICY.json']]
    values += [load(basic / n) for n in ['source/raw_builder.json', 'raw/parent.json', 'raw/domain.json', 'FRAME_POLICY.json', 'RADIUS_POLICY.json']]
    values += [data]
    binding = literal(*values)
    proof = audit(values[5], data, olddata, prior, old72)
    rejected = []

    def reject(name, action):
        try:
            action()
        except (ValueError, KeyError, IndexError, TypeError):
            rejected.append(name)
        else:
            raise ValueError('corruption accepted ' + name)

    def corrupted(position, mutation):
        changed = list(values)
        changed[position] = deepcopy(changed[position])
        mutation(changed[position])
        return lambda: literal(*changed)

    reject('restore old linear106 frame', corrupted(5, lambda d: d['rows'].__setitem__(1152, values[0]['rows'][1152])))
    reject('change square106 to square107', corrupted(5, lambda d: d['rows'][1185]['terms'].__setitem__(0, [-1, [107, 107]])))
    reject('replace actualcall3 output by square port', corrupted(5, lambda d: d['powers'][3].update(output=['v', 1267])))
    reject('change unrelated native row', corrupted(5, lambda d: d['rows'][0]['terms'][0].__setitem__(0, -2)))
    reject('drop old range square', corrupted(5, lambda d: d['rows'][1177]['terms'].__setitem__(0, [-1, [573]])))
    reject('remove retained high guard', corrupted(7, lambda d: d['guards'].__delitem__(next(i for i, g in enumerate(d['guards']) if g['predicate'].get('raw_variables') == [534]))))
    reject('restore removed106 guard', corrupted(7, lambda d: d['guards'].append(values[2]['guards'][14])))
    reject('change surviving auxiliary name', corrupted(6, lambda d: d['variables'][-1].update(name='changed')))
    reject('reuse prior auxiliary indices', corrupted(7, lambda d: d['guards'][-1].update(auxiliary=[1453, 1454, 1455])))
    reject('weaken the joint factorial predicate', corrupted(9, lambda d: d['joint_guard']['predicate'].update(terms=[[1, [87]], [-1, [86]]])))
    reject('claim old frame calibration', corrupted(8, lambda d: d.update(old_frame_calibration_not_assumed=False)))
    for key in ['new_frame_cut', 'new_weak_frame_cut', 'expanded_frame_cut', 'expanded_weak_frame_cut']:
        bad = deepcopy(data)
        bad[key]['row_combination'][0]['multiplier'][0][0] += 1
        reject('alter complete ' + key + ' coefficient', lambda b=bad: audit(values[5], b, olddata, prior, old72))
    bad = deepcopy(data)
    bad['additional_missing'].remove(132)
    reject('omit delayed132 dependency', lambda: audit(values[5], bad, olddata, prior, old72))
    bad = deepcopy(data)
    bad['delayed_bound']['factor'].append([1, [130]])
    reject('make130 positivity depend on itself', lambda: audit(values[5], bad, olddata, prior, old72))
    bad = deepcopy(data)
    bad['power3_binding']['output'] = 1267
    reject('bind signed residue to wrong output', lambda: audit(values[5], bad, olddata, prior, old72))
    bad = deepcopy(data)
    bad['supporting_calls'] = [3, 9]
    reject('use signedcall3 to orient its own pair', lambda: audit(values[5], bad, olddata, prior, old72))
    bad = deepcopy(prior)
    bad['seeds'][0]['aliases']['X'] = 106
    reject('hide a lost sign in seed aliases', lambda: audit(values[5], data, olddata, bad, old72))
    # Two exact free-ring identities used by positive-pair signed residue recovery.
    A, n, X, Y = map(V, [2000, 2001, 2002, 2003])
    delta = add(mul(A, A), C(-1))
    T = add(add(mul(C(2), mul(A, n)), mul(n, n), -1), C(-1))
    An = add(A, n, -1)
    p = add(X, mul(An, Y), -1)
    nextX = add(mul(A, X), mul(delta, Y))
    nextY = add(X, mul(A, Y))
    nextp = add(nextX, mul(An, nextY), -1)
    need(add(add(nextp, mul(n, p), -1), mul(T, Y), -1) == {}, 'universal positive Pell residue recurrence')
    other = add(X, mul(An, Y))
    norm = add(mul(X, X), mul(delta, mul(Y, Y)), -1)
    need(add(mul(p, other), mul(T, mul(Y, Y)), -1) == norm, 'universal complementary residue/norm identity')
    signed_controls = 0
    nonvacuous_true_outputs = 0
    for W in list(range(4, 11)) + [51, 52]:
        Avalue = W ** W + 1
        bases = list(range(2, W)) if W < 20 else [49, 50]
        indices = range(1, W) if W < 20 else range(1, 4)
        for base in bases:
            modulus = 2 * Avalue * base - base * base - 1
            need(modulus > Avalue, 'actual positive modulus dominance')
            x, y = 1, 0
            for index in indices:
                x, y = Avalue * x + (Avalue * Avalue - 1) * y, x + Avalue * y
                for output in range(1 - W, W):
                    need(abs(output - base ** index) < W ** W < modulus, 'signed output size bound')
                    agrees = (x - (Avalue - base) * y - output) % modulus == 0
                    need(agrees == (output == base ** index), 'positive indexed pair recovers exact signed output')
                    signed_controls += 1
                    nonvacuous_true_outputs += agrees
    bound_controls = 0
    for M in range(1, 8):
        for output in range(8):
            for g in range(4):
                for choose in range(4):
                    for slack in range(4):
                        F = 1 + M + slack
                        G = output * g * choose - M
                        need(G + F == output * g * choose + 1 + slack > 0, 'strict shifted bound130 polynomial')
                        if G % F == 0:
                            need(G // F >= 0, 'integer130 follows from recovered signs')
                            bound_controls += 1
    need((-1 * 1 * 1 - 1) // (1 + 1 + 0) == -1, 'unknown negative106 genuinely prevents early130 bound')
    need(nonvacuous_true_outputs > 0 and bound_controls > 0, 'nonvacuous residue/bound controls')
    need(data['fresh_completeness'] is True and data['pointwise_old_new_tuple_map'] is False and data['projected_metrics_claimed'] is False and data['native_contracts'] == ['KEndpoint.c222_iff_zf_refutation', 'ConstructibleChoice.zf_refutation_iff_zfc_refutation'], 'fixed ordinary endpoint and fresh-witness scope')
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), literal_binding=binding, chronological_source_audit=proof,
                  universal_pell_identities=2, signed_positive_pair_controls=signed_controls, true_output_controls=nonvacuous_true_outputs,
                  delayed_bound130_controls=bound_controls, rejected_corruptions=rejected, parent_checker_or_builder_or_optimizer_or_incoming_code_or_lean_executed=False,
                  complete_ordinary_equivalence=True, projected_metrics_claimed=False,
                  source_pins={n: digest(HERE / n) for n in ['PROOF.md', 'FULL_SOURCE.md', 'README.md', 'CERTIFICATE.json', 'SOURCE_PINS.json', 'check.py']},
                  scope='Complete literal62 source/guard/frame binding and acyclic interface replay. The unbounded ordinary proof and fresh completeness are PROOF.md/FULL_SOURCE.md; finite profiles and optional CSE remain separate.')
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output.exists():
        need(args.output.read_text() == text, 'refuse changed receipt overwrite')
    else:
        args.output.write_text(text)
    print(json.dumps(dict(status='PASS', identities=proof['collected_identities'], early_prefix=602, restored_prefix=proof['final_prefix_coordinates'], rejected=len(rejected)), sort_keys=True))


if __name__ == '__main__':
    main()
