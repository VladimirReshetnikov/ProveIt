#!/usr/bin/env python3
"""Inert stdlib-only verification of the complete helper reflection interface.

Execution is held until full code review. No incoming module is imported.
"""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / 'con-zfc-diophantine-forms/125-unified-binomial-round15/direct/unified_reparam_derived_shell'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def get(p):
    return json.loads(p.read_text())


def digest(p):
    return sha256(p.read_bytes()).hexdigest()


def poly(terms):
    out = {}
    for c, m in terms:
        need(type(c) is int and all(type(i) is int and i >= 0 for i in m), 'integer polynomial')
        m = tuple(sorted(m)); out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def add(*items):
    return poly([[c, list(m)] for p in items for m, c in p.items()])


def mul(a, b):
    return poly([[c*d, list(m+n)] for m, c in a.items() for n, d in b.items()])


def scale(a, c):
    return {m: d*c for m, d in a.items() if d*c}


def v(i):
    return {(i,): 1}


def terms(p):
    return [[c, list(m)] for m, c in sorted(p.items())]


def reflect(p, rules):
    out = {}
    for m, c in p.items():
        a = {(): c}
        for i in m:
            a = mul(a, rules.get(i, v(i)))
        out = add(out, a)
    return out


def verify(source, guarded, transform, cert):
    need((len(source['variables']), len(source['residuals'])) == (522, 446), 'whole source shape')
    need(guarded['variables'][:522] == source['variables'] and guarded['residuals'][:446] == source['residuals'], 'whole original body prefix')
    need((len(guarded['variables']), len(guarded['residuals'])) == (636, 484), 'whole old guard layout')
    rules = {251: { (251,): -1}, 252: {(): -2, (252,): -1},
             510: {(): -2, (510,): -1}, 254: {(254,): -1}, 511: {(511,): -1}}
    need(cert['reflection'] == {str(i): terms(p) for i, p in rules.items()}, 'exact affine involution')
    fixed = [i for i in range(522) if i not in rules]
    need(cert['fixed_body_coordinates'] == fixed and cert['body_rows'] == list(range(446)), 'whole fixed complement/row maps')
    for i in range(522):
        need(reflect(reflect(v(i), rules), rules) == v(i), 'affine involution on all coordinates')
    hits = {str(i): [j for j, row in enumerate(source['residuals']) if any(i in m for c, m in row['terms'])] for i in rules}
    expected_hits = {'251': [205,206,207,434], '252': [207], '510': [433], '254': [205,206], '511': [433,434]}
    need(hits == expected_hits == cert['changed_coordinate_occurrences'], 'complete actual private occurrence maps')
    local = {205: [[-1,[246,251]],[1,[254]]],
             206: [[-1,[]],[1,[250,250]],[1,[251,251]],[-1,[254,254]]],
             207: [[-4,[251]],[-4,[251,252]],[1,[255]]],
             433: [[-1,[509]],[-1,[509,510]],[1,[511]]],
             434: [[1,[251]],[-1,[511]]]}
    need(cert['local_rows'] == {str(i): source['residuals'][i] for i in local}, 'literal five-row certificate')
    for i, p in local.items():
        need(poly(source['residuals'][i]['terms']) == poly(p), 'exact normalization relation')
    signs = [-1 if i in [205,433,434] else 1 for i in range(446)]
    need(cert['row_reflection_signs'] == signs, 'all446 row signs')
    sos, reflected_sos = {}, {}
    for i, row in enumerate(source['residuals']):
        p = poly(row['terms'])
        need(all(len(m) <= 2 and all(j < 522 for j in m) for m in p), 'quadratic fixed-body coordinates')
        q = reflect(p, rules)
        need(q == scale(p, signs[i]), 'complete row reflection identity ' + str(i))
        sos = add(sos, mul(p,p)); reflected_sos = add(reflected_sos, mul(q,q))
    need(sos == reflected_sos, 'whole body SOS exactly invariant')
    guards = transform['guards']; need(len(guards) == 38 and cert['old_guards'] == guards, 'all old guards')
    need([a for g in guards for a in g['auxiliary']] == list(range(522,636)), 'disjoint exhaustive old triples')
    references = {}
    for j, g in enumerate(guards):
        expr = poly(g['expression'])
        if g['kind'] == 'nonnegative':
            need(type(g['coordinate']) is int and 0 <= g['coordinate'] < 522 and expr == v(g['coordinate']), 'scalar predicate target')
        elif g['kind'] == 'paired_interval':
            need(len(g['pair']) == 2 and len(set(g['pair'])) == 2 and all(type(i) is int and 0 <= i < 522 for i in g['pair']) and expr == mul(v(g['pair'][0]),v(g['pair'][1])), 'individual product target')
        else:
            need(g['kind'] == 'positive_common_V' and expr == add(v(251), {():-1}), 'strict common ordinate target')
        a,b,c = g['auxiliary']; rid = 446+j
        need(g['row'] == rid and guarded['residuals'][rid]['label'] == 'domain_guard.'+str(j), 'old graph row')
        need(poly(guarded['residuals'][rid]['terms']) == add(expr,poly([[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]])), 'whole Legendre graph')
        for aux in [a,b,c]:
            need([i for i,row in enumerate(guarded['residuals']) if any(aux in m for co,m in row['terms'])] == [rid], 'old auxiliary has no escaping use')
        references[str(j)] = sorted({i for m in expr for i in m} & set(rules))
        if j not in [27,30]:
            need(not references[str(j)] and reflect(expr,rules) == expr, 'every remaining predicate fixed')
    need(references == cert['guard_changed_port_references'], 'whole predicate occurrence certificate')
    need(guards[27]['coordinate'] == 252 and guards[27]['auxiliary'] == [603,604,605]
         and guards[30]['auxiliary'] == [612,613,614] and cert['omitted_guards'] == [guards[27],guards[30]], 'exact two old omissions')
    need(guards[2]['coordinate'] == 3 and guards[25]['coordinate'] == 246, 'F/A guards fixed and distinct')
    new = add(v(255), {():-4})
    need(poly(cert['new_predicate']) == new and reflect(new,rules) == new, 'new affine comparison-base lower bound')
    calls = transform['square_budget']['power_calls']; atoms = transform['square_budget']['atoms']
    need(cert['power_calls'] == calls and cert['frame_atoms'] == atoms and len(calls) == 18 and len(atoms) == 37, 'whole semantic port inventory')
    need(all(not set(rules).intersection(m) for call in calls for p in call.values() for co,m in p)
         and all(not set(rules).intersection(m) for atom in atoms for co,m in atom['affine']), 'all requested/frame semantic ports fixed')
    need(cert['normalization_cases'] == {'V>0':'identity', 'V<0':'reflection', 'V=0':'excluded by row207 and new predicate'}, 'normalization case schedule')
    need(cert['witness_schedule'] == ['normalize_V_and_d','restore_old_d_and_V_triples','apply_matching_F_or_joint_theorem_only_if_needed','restore_optional_F_A_triples'], 'ordered ordinary composition')
    need(cert['variant_omissions'] == {'baseline':[], 'F_only':[2], 'joint_F_A':[2,25]}, 'appropriate ordinary variants')
    need(cert['witness_maps'] == dict(
        old_to_new=dict(body='identity', retained_old_guard_witnesses='identity', discard_old_triples=[27,30], new_triple='fresh Legendre witnesses for v255-4'),
        new_to_old=dict(body='identity if V>0, reflection if V<0', retained_old_guard_witnesses='identity', restore_old_triples=[27,30], old_triples='fresh Legendre witnesses for normalized d and normalized V-1'),
        fixed_body_coordinates=fixed), 'both existential witness maps and fixed complement')
    return dict(body_rows=446, body_variables=522, row_involution_identities=446, coordinate_involution_identities=522,
                old_guard_graphs=38, whole_body_sos_invariant=True, changed_body_coordinates=sorted(rules),
                fixed_semantic_power_interfaces=18, fixed_frame_atoms=37)


def controls(data, cert):
    trials = []
    for i in [205,206,207,433,434]:
        d = deepcopy(data); d[0]['residuals'][i]['terms'].append([1,[]]); d[1]['residuals'][i] = deepcopy(d[0]['residuals'][i])
        trials.append(('local_row_'+str(i), d, cert))
    for coordinate in [251,252,254,510,511,603]:
        d = deepcopy(data); d[0]['residuals'][100]['terms'].append([1,[coordinate]]); d[1]['residuals'][100] = deepcopy(d[0]['residuals'][100])
        trials.append(('escaping_coordinate_'+str(coordinate),d,cert))
    c = deepcopy(cert); c['reflection']['252'] = [[-1,[]],[-1,[252]]]
    trials.append(('wrong_d_reflection',data,c))
    c = deepcopy(cert); c['reflection']['510'] = [[-1,[510]]]
    trials.append(('wrong_e_reflection',data,c))
    c = deepcopy(cert); c['row_reflection_signs'][205] = 1
    trials.append(('wrong_row_sign',data,c))
    c = deepcopy(cert); c['new_predicate'] = [[1,[255]]]
    trials.append(('missing_Bc_lower_bound',data,c))
    d = deepcopy(data); c = deepcopy(cert); j = 6; g = d[2]['guards'][j]
    g['coordinate'] = 251; g['expression'] = [[1,[251]]]; c['old_guards'][j] = deepcopy(g)
    a,b,z = g['auxiliary']; d[1]['residuals'][g['row']]['terms'] = [[1,[251]],[-1,[a,a]],[-1,[b,b]],[-1,[z,z]],[-1,[z]]]
    trials.append(('changed_port_in_retained_predicate',d,c))
    c = deepcopy(cert); c['witness_schedule'][2] = 'invoke_F_only_theorem_with_A_absent'
    trials.append(('invalid_F_only_composition',data,c))
    c = deepcopy(cert); c['witness_maps']['new_to_old']['body'] = 'identity on the whole body'
    trials.append(('false_fixed_whole_body_inverse',data,c))
    rejected = []
    for name,d,c in trials:
        try:
            verify(*d,c)
        except (ValueError,KeyError,IndexError,TypeError) as error:
            rejected.append(dict(name=name,reason=str(error)))
        else:
            raise ValueError('corruption accepted: '+name)
    return rejected


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--output',type=Path,required=True); args = ap.parse_args()
    pins = get(HERE/'SOURCE_PINS.json')
    for name,want in pins['files'].items():
        need(digest(ROOT/name) == want, 'whole source pin '+name)
    for name,want in pins['core'].items():
        need(digest(HERE/name) == want, 'own core pin '+name)
    for name,want in pins['closed_dependencies'].items():
        p = ROOT/name; need(digest(p/'MANIFEST.json') == want, 'closed parent pin')
        need({str(q.relative_to(p)):digest(q) for q in p.rglob('*') if q.is_file() and q!=p/'MANIFEST.json'} == get(p/'MANIFEST.json')['files'], 'complete closed dependency')
    data = [get(PARENT/n) for n in ['source.json','guarded.json','transform_certificate.json']]; cert = get(HERE/'CERTIFICATE.json')
    result = verify(*data,cert); rejected = controls(data,cert)
    manifest = HERE/'MANIFEST.json'
    if manifest.exists():
        need({str(q.relative_to(HERE)):digest(q) for q in HERE.rglob('*') if q.is_file() and q!=manifest} == get(manifest)['files'], 'complete own closed inventory')
    report = dict(status='PASS',optimized=not __debug__,source_pins_sha256=digest(HERE/'SOURCE_PINS.json'),literal=result,
                  actual_corruptions=rejected,incoming_code_imported_or_executed=False,source_or_projection_generated=False,
                  scope='Ordinary helper normalization; five private body coordinates may change; no new projected metrics.')
    out = json.dumps(report,indent=2,sort_keys=True)+'\n'; need(not args.output.exists() or args.output.read_text()==out,'different existing output')
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_text(out)
    print(json.dumps(dict(status='PASS',rows=446,actual_corruptions=len(rejected)),sort_keys=True))


if __name__ == '__main__':
    main()
