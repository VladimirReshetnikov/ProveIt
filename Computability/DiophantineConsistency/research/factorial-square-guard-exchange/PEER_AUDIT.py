#!/usr/bin/env python3
"""Independent stdlib audit: ordinary bridge to the frozen literal RAW parent.

No author checker, builder, optimizer, archive code or Lean is imported/run.
The unbounded proof is reviewed separately in PEER_REVIEW.md.
"""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from math import comb, factorial
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_bytes())


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def poly(terms):
    result = {}
    for coefficient, monomial in terms:
        require(type(coefficient) is int and all(type(v) is int for v in monomial), 'integer terms')
        key = tuple(sorted(monomial))
        result[key] = result.get(key, 0) + coefficient
    return {m: c for m, c in result.items() if c}


def add(left, right):
    result = dict(left)
    for m, c in right.items():
        result[m] = result.get(m, 0) + c
    return {m: c for m, c in result.items() if c}


def multiply(left, right):
    result = {}
    for m, c in left.items():
        for n, d in right.items():
            key = tuple(sorted(m + n))
            result[key] = result.get(key, 0) + c*d
    return {m: c for m, c in result.items() if c}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    binding = read(HERE/'PEER_BINDING.json')
    for name, expected in binding['files'].items():
        require(digest(ROOT/name) == expected, 'exact whole-file pin: '+name)
    prototype = ROOT/'research/squared-radius-source-prototype'
    manifest = read(prototype/'MANIFEST.json')['files']
    require({str(p.relative_to(prototype)) for p in prototype.rglob('*') if p.is_file() and p.name != 'MANIFEST.json'} == set(manifest), 'closed prototype inventory')
    for name, expected in manifest.items():
        require(digest(prototype/name) == expected, 'entire frozen prototype: '+name)
    if (HERE/'MANIFEST.json').exists():
        own_manifest = read(HERE/'MANIFEST.json')['files']
        require({str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p.name != 'MANIFEST.json'} == set(own_manifest), 'closed ordinary packet')
        for name, expected in own_manifest.items():
            require(digest(HERE/name) == expected, 'sealed ordinary member: '+name)

    original = read(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    source = read(prototype/'source/raw_builder.json')
    cert = read(HERE/'CERTIFICATE.json')
    expected = deepcopy(original)
    expected['rows'][75]['terms'] = [[-1, [87, 87]], [1, [89]]]
    require(source == expected and len(source['rows']) == 1177 and len(source['variables']) == 1259, 'complete source equality except terms of row75')
    require(cert['changed_rows']['75'] == {'old': original['rows'][75], 'new': source['rows'][75]}, 'ordinary theorem binds actual prototype row')
    require(source['rows'][74] == original['rows'][74], 'private K square kept')
    require(source['rows'][75]['label'] == 'multiplication', 'original row label')
    parent_dir = ROOT/'research/shifted-t-index-guard-profile/raw'
    old_parent, parent = read(parent_dir/'parent.json'), read(prototype/'raw/parent.json')
    old_domain, domain = read(parent_dir/'domain.json'), read(prototype/'raw/domain.json')
    expected = deepcopy(old_parent)
    expected['residuals'][75]['terms'] = source['rows'][75]['terms']
    expected['residuals'][1248]['terms'] = [[1,[87]],[-1,[86]],[-1,[1472,1472]],[-1,[1473,1473]],[-1,[1474,1474]],[-1,[1474]]]
    require(old_parent['variant'] == 'shifted_t_index_guard72_raw', 'exact old provenance tag')
    expected['variant'] = 'squared_radius_f_ge_K_raw72_literal_prototype'
    require(parent == expected, 'whole parent changes only two rows and explicit provenance tag, preserving all labels/variables')
    require(domain['guards'][:-1] == old_domain['guards'][:-1], 'all other71 predicates and auxiliaries identical')
    require(domain['guards'][-1] == {'auxiliary':[1472,1473,1474], 'predicate':{'kind':'factorial_index_lower_bound','raw_variables':[87,86],'terms':[[1,[87]],[-1,[86]]]}}, 'exact final f-K predicate')
    require(domain['baseline_raw_indices'] == list(range(1259)) and len(domain['guards']) == 72, 'all raw coordinates/72 guards')
    require(parent['variables'] == old_parent['variables'] and len(parent['variables']) == 1475, 'all auxiliary names and numbers retained')
    require(len(parent['residuals']) == 1249, 'entire parent row list')
    for row, guard in zip(parent['residuals'][1177:], domain['guards']):
        a, b, c = guard['auxiliary']
        graph = add(poly(guard['predicate']['terms']), poly([[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]))
        require(poly(row['terms']) == graph, 'each of72 complete three-square graph polynomials')
    scalar = [g['predicate']['raw_variables'][0] for g in domain['guards'] if g['predicate']['kind'] == 'retained_scalar']
    require(sorted(scalar) == cert['retained_original_guard_indices'] and len(scalar) == 69, 'all69 scalar guards match theorem')
    require(cert['new_factorial0_guard'] == {'kind':'nonnegative_difference','left_raw_variable':87,'right_raw_variable':86}, 'new ordinary predicate matches graph')

    rows = [poly(row['terms']) for row in source['rows']]
    identities = 0
    def collect(cut, target=None):
        nonlocal identities
        actual = {}
        for item in cut['row_combination']:
            actual = add(actual, multiply(poly(item['multiplier']), rows[item['row']]))
        desired = poly(cut.get('polynomial', cut.get('expanded_polynomial'))) if target is None else poly(target)
        require(actual == desired, 'independent full-coefficient row ideal')
        identities += 1

    for cut in cert['early_cuts'].values():
        collect(cut)
    collect(cert['proposed_radius_cut'], [[1,[89]],[-1,[87,87]]])
    for cut in cert['unchanged_local_cuts'].values():
        collect(cut)
    for v in range(64, 87):
        require(rows[v-13] == poly([[1,[v]],[-1,[v-1,v-1]]]), '23 squares independent of f')
    require(cert['changed_sign_step'] == {'coefficient':1,'dependencies':[],'kind':'positive_monomials','rhs':[[1,[87,87]]],'row':75,'variable':89}, 'sign89 depends on square only')
    prior = read(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    old72 = read(ROOT/'research/shifted-t-index-guard/CERTIFICATE.json')
    require(all(q['variable'] != 89 and 89 not in q['positive_monomial'] for q in prior['positive_prefix']['steps']), 'unchanged inherited strict list does not presume positive89')
    require(7 not in old72['chronology']['interpreted_calls_before_825'], 'call7 excluded before shifted-t restoration')
    ports = [[5,4,6],[92,86,93],[103,4,104],[87,4,106],[112,4,113],[531,90,532],[530,86,533],[531,110,546],[530,4,547],[531,122,560],[531,44,573],[530,5,574],[531,46,583],[531,48,591],[531,50,599],[531,52,607],[530,36,608],[531,54,617],[531,56,625],[530,136,626],[531,58,635]]
    require([[q[k][1] for k in ['base','exponent','output']] for q in source['powers']] == ports, 'all21 actual source power ports')
    for call, port in zip(prior['power_calls'], ports):
        base, exponent, output = port
        require([call[k] for k in ['base','exponent','output']] == port, 'power source/cut aliases')
        collect(call['cut'], [[1,[call['X']]],[-1,[644,call['Y']]],[1,[base,call['Y']]],[-1,[output]],[-1,[call['modulus'],call['quotient']]]])
    require(len(source['seeds']) == len(prior['seeds']) == 15 and len(source['indices']) == 16, 'all indexed seeds and atoms')
    for actual, seed in zip(source['seeds'], prior['seeds']):
        require(actual['exponent'] == ['v',seed['aliases']['k']] and actual['pair'] == [['v',seed['aliases'][k]] for k in ['X','Y']], 'every actual seed interface')
        for cut in seed['cuts'].values():
            collect(cut)
    for item in prior['moduli']:
        collect(item['cut'])
    for name in ['bootstrap_norm','unit_norm_cut','comparison_base_constructor','comparison_base_congruence']:
        collect(prior[name])
    for name in ['frame_cut','weak_frame_cut']:
        collect(old72[name])
    upper = [44,46,48,50,52,54,56,58]
    lower = [5,5,5,5,36,36,136,136]
    targets = {'aggregate':[[1,[v]] for v in upper+[519]]+[[-8,[129]]],
      't_successor':[[1,[5]],[-1,[4]],[-1,[]]], 'y_successor':[[1,[36]],[-1,[2]],[-1,[]]], 'x_successor':[[1,[136]],[-1,[1]],[-1,[]]],
      'derived_discriminant':[[1,[917]],[-1,[644,644]],[1,[]]], 'derived_X':[[1,[921]],[-1,[644,670]],[-1,[644,644,671]],[1,[671]]], 'derived_Y':[[1,[922]],[-1,[670]],[-1,[644,671]]]}
    for name, target in targets.items():
        collect(cert['full_source_cuts'][name], target)
    require([(r[0][1],r[1][1],r[2][1]) for r in source['ranges']] == list(zip(upper,lower,[129]*8)), 'actual eight range ports')
    require(source['derivations'] == [{'kind':'shift','pair':[['v',921],['v',922]],'shift':1,'source':['v',4],'target':['v',5]}], 'one derived successor pair')
    for interface in cert['fused_range_interfaces']:
        n,k,num,den,q,rem,slack = [interface[key] for key in ['upper','lower','numerator','denominator','quotient','remainder','slack']]
        require([531,n,num] in ports and [530,k,den] in ports, 'fused ports are actual interpreted power requests')
        collect(interface['quotient_cut'], [[1,[num]],[-1,[129,den,q]],[-1,[rem]]])
        collect(interface['remainder_cut'], [[1,[den]],[-1,[rem]],[-1,[slack]],[-1,[]]])

    corruptions = []
    def reject(label, action):
        try:
            action()
        except ValueError:
            corruptions.append(label)
        else:
            raise ValueError('accepted deliberate corruption: '+label)
    bad_source = deepcopy(source)
    bad_source['rows'][75] = original['rows'][75]
    reject('old radius row', lambda: require(bad_source == source, 'source mismatch'))
    bad_source = deepcopy(source)
    bad_source['rows'][74]['terms'] = [[1,[88]]]
    reject('delete private square', lambda: require(bad_source == source, 'source mismatch'))
    bad_parent = deepcopy(parent)
    bad_parent['residuals'][1248] = old_parent['residuals'][1248]
    reject('restore old f>=2 graph', lambda: require(bad_parent == parent, 'parent mismatch'))
    bad_parent = deepcopy(parent)
    bad_parent['variables'][1474]['name'] += '.changed'
    reject('rename guard auxiliary', lambda: require(bad_parent == parent, 'parent mismatch'))
    bad_cut = deepcopy(cert['full_source_cuts']['aggregate'])
    bad_cut['row_combination'][0]['multiplier'][0][0] += 1
    reject('alter aggregate coefficient', lambda: collect(bad_cut, targets['aggregate']))
    reject('wrong lower index alias', lambda: collect(cert['full_source_cuts']['y_successor'], [[1,[36]],[-1,[3]],[-2,[]]]))
    reject('wrong derived Pell addition', lambda: collect(cert['full_source_cuts']['derived_Y'], [[1,[922]],[-1,[670]],[1,[644,671]]]))
    reject('drop fused remainder unit', lambda: collect(cert['fused_range_interfaces'][-1]['remainder_cut'], [[1,[626]],[-1,[637]],[-1,[638]]]))
    reject('early call7 interpretation', lambda: require(7 in old72['chronology']['interpreted_calls_before_825'], 'chronology mismatch'))

    ceiling_controls = 0
    for k in range(4, 16):
        m = factorial(k)
        for f in sorted({k,k+1,m-1,m,m+1,2*m}):
            numerator, denominator = (f*f+1)**k, comb(f*f+k,k)
            require(((numerator+denominator-1)//denominator == f) == (f == m), 'independent exact ceiling controls')
            ceiling_controls += 1
    for t in range(1, 11):
        R = t+6
        K = R*R
        f = K
        B = (1+(t+1)*f)**t
        Q = f*(B+2)-1
        require(8*Q < 24*R**t*f**(t+1) <= f**(2*t+2), 'acyclic range bound diagnostic')
        require(comb(8*Q, R) < (1+f*f)**K, 'all-lower-degree worst-port range diagnostic')
    result = {'status':'PASS','optimized_python':bool(sys.flags.optimize), 'source_rows':1177,'source_coordinates':1259,'literal_parent_rows':1249,'literal_parent_coordinates':1475,'predicates':72,'guard_graphs_checked':72,'complete_row_identities':identities,'power_ports':21,'seed_ports':15,'range_ports':8,'derived_pairs':1,'exact_ceiling_controls':ceiling_controls,'direct_range_controls':10,'rejected_corruptions':corruptions,'prototype_manifest_sha256':digest(prototype/'MANIFEST.json'),'binding_sha256':digest(HERE/'PEER_BINDING.json'),'audit_sha256':digest(Path(__file__)),'author_checker_imported_or_executed':False,'builder_optimizer_archive_code_or_lean_executed':False,'projected_metrics_claimed':False,'scope':'Independent complete literal bridge and selected full-coefficient interfaces; unbounded ordinary proof reviewed in PEER_REVIEW.md.'}
    output = json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():
        require(args.output.read_text() == output, 'refuse changed receipt overwrite')
    else:
        args.output.write_text(output)
    print(output,end='')


if __name__ == '__main__':
    main()
