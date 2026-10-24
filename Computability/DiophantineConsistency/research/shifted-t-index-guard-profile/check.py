#!/usr/bin/env python3
"""Optimizer-free72 domains, shifted-t chronology, integer inverses and full quartics."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from review_synchronized_certificates import full_sos


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def digest(data):
    return sha256(data).hexdigest()


def module(name, path):
    spec = importlib.util.spec_from_file_location(name,path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def reject(name, action):
    try:
        action()
    except (ValueError,RuntimeError,KeyError,IndexError,TypeError):
        return name
    raise ValueError('corruption accepted '+name)


def source_interface(report):
    need(report['status'] == 'PASS' and report['source_predicates'] == 72,
         'pinned ordinary72 source checker and reviewed shifted-t branch')
    need(report['complete_original_row_identities'] == 95 and
         report['ordered_sign_steps'] == 573 and report['strict_constructor_steps'] == 429 and
         report['nonnegative_prefix_coordinates'] == 641 and
         report['actual_frame_arguments'] == 43 and report['frame_contains59'] is False and
         report['sole_possible_negative_actual_argument'] == 104 and report['positive_successor'] == 105 and
         report['source_occurrences_of104'] == [88,693,1151] and
         report['skipped_source_sign_rows'] == [88,114] and report['frame_contains825'] is False and
         report['source_occurrences_of825'] == [762],
         'explicit modified641-prefix and actual43-argument weak frame before source calibration')
    need(report['actual_call_interfaces'] == list(range(10)) and
         report['actual_calls_used_before_B_recovery'] == [0,2,9] and
         report['actual_calls_interpreted_before825'] == [0,1,2,3,4,5,6,8,9] and
         report['factorial1_semantics_used'] is False and
         report['nonnegative_support_call_outputs'] == [6,560] and
         report['source_builder_optimizer_or_emitter_executed'] is False and
         report['projected_equation_or_metrics_claimed'] is False,
         'call7 excluded until collapse; no factorial1 or full73 source semantics before825 recovery')
    for name,expected in report['source_pins'].items():
        need(digest((ROOT/name).read_bytes()) == expected,'whole independent source peer pin '+name)
    return dict(status='PASS',source_predicates=72,modified_nonnegative_prefix_coordinates=641,
        ordered_sign_steps=573,strict_constructor_steps=429,actual_frame_arguments=43,
        raw59_in_frame=False,sole_possibly_negative_argument=104,positive_successor=105,
        safe_seed_orientation_calls=[0,9],safe_support_outputs=[6,560],final_negative_branch_call=2,
        early_B_seed_recovery_only_under_B_minus_one=True,
        interpreted_calls_before825=[0,1,2,3,4,5,6,8,9],
        call7_interpreted_only_after_collapsed_seed_exclusion=True,
        factorial1_semantics_used=False,full73_chain_only_after_raw825_recovery=True,
        source_identity_count=95,ordinary_proof='research/shifted-t-index-guard/PROOF.md',
        full_parent_restoration_required_before_source_semantics=True)


def independent_peer_interface(report):
    need(report['status'] == 'PASS' and report['independent_original_row_cuts'] == 15 and
         report['source_occurrences_of825'] == [762] and
         report['actual_ports'] == {'4':[112,4,113],'7':[531,110,546],'8':[530,4,547]} and
         report['interpreted_calls_before825'] == [0,1,2,3,4,5,6,8,9] and
         report['exact_t1_identity_without_factorial1_semantics'] is True and
         report['ordinary_source_equivalence_approved'] is True and
         report['imports_author_poly_or_checker'] is False and
         report['source_builder_optimizer_archive_or_lean_executed'] is False,
         'independent stdlib15-cut audit, actual ports, t1 identity and strict chronology')
    for name,expected in report['author_source_pins'].items():
        need(digest((ROOT/'research/shifted-t-index-guard'/name).read_bytes()) == expected,
             'whole independent peer author source binding '+name)
    return dict(status='PASS',independent_original_row_cuts=15,
        exact_t1_identity_without_factorial1_semantics=True,imports_author_poly_or_checker=False,
        interpreted_calls_before825=[0,1,2,3,4,5,6,8,9])


def shifted_t_binding(data,raw,p):
    P,add,mul = p.poly,p.add,p.mul
    rows = [P(row['terms']) for row in raw['rows']]
    need([i for i,row in enumerate(rows) if any(825 in m for m in row)] == [762] and
         825 not in data['frame_arguments'],'complete newly omitted coordinate boundary')
    targets = {
        'd1_radius': [[1,[109]],[-1,[107,4,4]]],
        't_base': [[1,[112]],[-1,[109]],[-1,[]]],
        'factorial1_remainder': [[1,[111]],[-1,[114]],[-1,[115]],[-1,[]]],
        'factorial1_ceiling': [[1,[107,111]],[-1,[113]],[-1,[115]]],
        'choose1_digit': [[1,[546]],[-1,[547,111]],[-1,[547,530,548]],[-1,[549]]],
    }
    def collect(cut,target):
        out = {}
        for term in cut['row_combination']:
            need(type(term['row']) is int and 0 <= term['row'] < len(rows),'actual shifted-t source row')
            out = add(out,mul(P(term['multiplier']),rows[term['row']]))
        need(out == P(target) == P(cut['polynomial']),'entire independently recollected shifted-t source ideal')
        return out
    for name,target in targets.items():
        collect(data['exact_source_cuts'][name],target)
    combined = collect(data['t1_combined_source_cut'],[[1,[107,111]],[-1,[113]],[-1,[115]],
                        [1,[112]],[-1,[]],[-1,[107,4,4]]])
    at1 = {}
    for m,c in combined.items():
        at1 = add(at1,{tuple(v for v in m if v != 4):c})
    at1 = add(at1,P([[1,[113]],[-1,[112]]]))
    need(at1 == P([[1,[107,111]],[-1,[107]],[-1,[]],[-1,[115]]]),
         't1 relation g*(C1-1)=1+slack from only recovered call4')
    collect(data['seeds'][3]['cuts']['index_at_most_Y'],[[1,[822]],[-1,[110]],[-1,[825]]])
    chronology = data['chronology']
    need(chronology['interpreted_calls_before_825'] == [0,1,2,3,4,5,6,8,9] and
         chronology['calls_not_interpreted_before_825'] == [7] and
         chronology['known_slacks_after_factorial0_and_pairing'] == [674,711,779,861] and
         chronology['t1_branch_needs_factorial1_semantics'] is False and
         chronology['whole_parent73_theorem_used_only_after825_recovered'] is True,
         'exact partial-parent chronology and late guard restoration')
    return dict(complete_original_row_ideals=7,source_occurrences_of825=[762],
        exact_t1_identity_without_factorial1_semantics=True,
        interpreted_calls_before825=[0,1,2,3,4,5,6,8,9],
        call7_power_semantics_excluded_until_collapse_ruled_out=True)


def weak_frame_binding(data,raw,p):
    P,add,mul = p.poly,p.add,p.mul
    rows = [P(row['terms']) for row in raw['rows']]
    arguments = {call[key][1] for call in raw['powers'] for key in ('base','exponent','output')}
    need(len(arguments) == 43 and 104 in arguments and 59 not in arguments and
         data['frame_arguments'] == sorted(arguments) and
         data['weak_frame_nonnegative_arguments'] == sorted(arguments-{104}),
         'entire actual frame/weak frame role binding')
    def collect(cut,target):
        value = {}
        for item in cut['row_combination']:
            need(type(item['row']) is int and 0 <= item['row'] < len(rows),'literal weak-frame source row')
            value = add(value,mul(P(item['multiplier']),rows[item['row']]))
        need(value == target == P(cut['polynomial']),'complete independent weak-frame ideal')
    collect(data['frame_cut'],P([[1,[643]],[-2,[]]]+[[-1,[v]] for v in sorted(arguments)]))
    collect(data['weak_frame_cut'],P([[1,[643]],[-1,[105]]]+[[-1,[v]] for v in sorted(arguments-{104})]))
    collect(data['exact_source_cuts']['positive_B_successor'],P([[1,[87,105]],[-1,[129]],[-1,[131]],[-2,[]]]))
    collect(data['exact_source_cuts']['positive_k122_constructor'],P([[1,[122]],[-1,[4]],[-1,[105]]]))
    need(data['early_derived_bounds'] == {'87':2,'93':2,'105':1,'129':1,'137':0} and
         data['expected_prefix'] == dict(nonnegative_count=641,excluded_coordinates=[59,104],
                                        sign_steps=573,strict_steps=429),
         'no unproved B>=0 or D>=2 seeded into source-prefix interpretation')
    need(data['negative_branch'] == dict(B=-1,D=1,k122_minus_t=1,seed_recovery_is_conditional=True) and
         data['calls_used_before_B_recovery'] == [0,2,9] and data['support_calls_for_t_k122'] == [0,9],
         'conditional consecutive-index branch with exact safe support ports')
    calls = {call['index']:call for call in data['actual_calls']}
    need([(calls[i]['base'],calls[i]['exponent'],calls[i]['output']) for i in [0,2,9]] ==
         [(5,4,6),(103,4,104),(531,122,560)],'actual support/final call arguments')
    return dict(complete_original_row_ideals=4,other_nonnegative_actual_arguments=42,
        actual_frame_arguments=43,excluded_prefix_coordinates=[59,104],
        early_successor_lower_bound=1,negative_branch_consecutive_indices=True)


def domain(eq,cert,family,old,oldcert,raw,body,initial):
    n,nr = oldcert['baseline_body_variables'],oldcert['baseline_body_rows']
    indices = oldcert['baseline_raw_indices']
    mp = {v:i for i,v in enumerate(indices)}
    variables = raw['variables'] if family == 'raw' else body['variables']
    rows = [dict(label=r['label'],terms=r['terms']) for r in raw['rows']] if family == 'raw' else body['residuals']
    need(old['variables'][:n] == variables and old['residuals'][:nr] == rows,
         'frozen73 body is original source with all metadata and coefficients')
    need(eq['domain'] == 'unrestricted integers' and eq['variables'][:n] == variables and
         eq['residuals'][:nr] == rows,'all original body records preserved verbatim')
    need(cert['baseline_body_variables'] == n and cert['baseline_body_rows'] == nr and
         cert['baseline_raw_indices'] == indices,'whole original body/raw-coordinate map')
    deleted = [i for i,g in enumerate(oldcert['guards']) if g['predicate']['kind'] == 'retained_scalar'
               and g['predicate']['raw_variables'] == [825]]
    need(len(oldcert['guards']) == 73 and len(deleted) == 1 and
         cert['removed_original_scalar_guard'] == 825 and cert['retained_parent_predicates'] == 72 and
         cert['inherited_parent_removed_original_scalar_guard'] == oldcert['removed_original_scalar_guard'] == 104
         and cert['deleted_parent_guard_index'] == deleted[0], 'delete precisely original scalar825 from73')
    selected = [(i,g) for i,g in enumerate(oldcert['guards']) if i not in deleted]
    predicates = [g['predicate'] for i,g in selected]
    scalar = {p['raw_variables'][0] for p in predicates if p['kind'] == 'retained_scalar'}
    need(len(scalar) == 69 and len(initial) == 61 and set(initial)-scalar == {59,93,104}
         and {6,94,95,113,131,537,694} <= scalar,
         'exact58 direct initial signs and all early/bootstrap/shifted-t premises retained')
    need([p for p in predicates if p['kind'] != 'retained_scalar'] == [
        dict(kind='strict_common_V',raw_variables=[656],terms=[[1,[mp[656]]],[-1,[]]]),
        dict(kind='paired_index_slacks',raw_variables=[674,861],terms=[[1,[mp[674],mp[861]]]]),
        dict(kind='factorial_lower_bound',raw_variables=[87],terms=[[1,[mp[87]]],[-2,[]]])],
        'unchanged strictV/product/f>=2 predicates, including exact coefficients')
    need(len(eq['variables']) == n+216 and len(eq['residuals']) == nr+72 and len(cert['guards']) == 72,
         'complete72-predicate dimensions with no extra defining wire')
    for j,(old_index,old_guard) in enumerate(selected):
        a,b,c = range(n+3*j,n+3*j+3)
        p = old_guard['predicate']
        need(cert['guards'][j] == dict(predicate=p,auxiliary=[a,b,c]),
             'every exact retained predicate and complete fresh triple')
        need(eq['variables'][a:c+1] == [old['variables'][v] for v in old_guard['auxiliary']],
             'all surviving auxiliary metadata preserved verbatim from73')
        need(eq['residuals'][nr+j] == dict(label=old['residuals'][nr+old_index]['label'],
             terms=p['terms']+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]),
             'every complete quadratic guard row and old label, with only private indices shifted')
    return dict(original_body_variables=n,original_body_rows=nr,predicates=72,
        retained_original_scalar_predicates=69,initial_direct_semantic_signs=58,
        modified_prefix_coordinates_after_independent_recovery=641,
        only_deleted_parent_scalar_guard=825,remaining_predicate_metadata_preserved=True,
        additional_defining_wires=0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    if (HERE/'MANIFEST.json').exists():
        seal = load(HERE/'MANIFEST.json')['files']
        need(set(seal) == {str(p.relative_to(HERE)) for p in HERE.rglob('*')
                          if p.is_file() and p.name != 'MANIFEST.json'},'closed full profile inventory')
        for name,expected in seal.items():
            need(digest((HERE/name).read_bytes()) == expected,'sealed profile member '+name)
    pins = load(HERE/'SOURCE_PINS.json')
    for name,expected in pins['files'].items():
        need(digest((ROOT/name).read_bytes()) == expected,'whole frozen input '+name)
    predecessor = ROOT/'research/pow2-output-sign-profile'
    oldseal = load(predecessor/'MANIFEST.json')['files']
    need(set(oldseal) == {str(p.relative_to(predecessor)) for p in predecessor.rglob('*')
                         if p.is_file() and p.name != 'MANIFEST.json'},'closed frozen73 parent inventory')
    for name,expected in oldseal.items():
        need(digest((predecessor/name).read_bytes()) == expected,'complete frozen73 member '+name)
    build = load(HERE/'BUILD.json')
    need(digest((HERE/'build.py').read_bytes()) == build['generator_sha256'],'producer pin')
    for name,expected in build['files'].items():
        need(digest((HERE/name).read_bytes()) == expected,'whole generated equation/inverse/quartic '+name)
    # Replay both the focused95-identity source checker and separate stdlib
    # 15-cut peer before licensing the72 source interpretation. Neither
    # imports the producer, its optimizer, or historical emitter.
    peer = ROOT/'research/shifted-t-index-guard/check.py'
    reference = load(peer.with_name('VERIFICATION_OPTIMIZED.json' if sys.flags.optimize
                                     else 'VERIFICATION.json'))
    recovery = source_interface(reference)
    with tempfile.TemporaryDirectory(prefix='shifted-t72-source-replay-') as tmp:
        output = Path(tmp)/'peer.json'
        command = [sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])
        proc = subprocess.run(command+[str(peer),'--output',str(output)],capture_output=True,text=True)
        need(proc.returncode == 0,'reviewed modified-prefix/weak-frame scratch replay '+proc.stderr)
        need(load(output) == reference,'entire source replay agrees with pinned reviewed receipt')
    recovery['source_checker_replayed_into_scratch'] = True
    recovery['source_checker_receipt_sha256'] = digest(json.dumps(
        {k:v for k,v in reference.items() if k != 'optimized_python'},sort_keys=True).encode())
    independent_script = peer.with_name('PEER_AUDIT.py')
    independent_reference = load(peer.with_name('PEER_INDEPENDENT_OPTIMIZED.json' if sys.flags.optimize
                                                else 'PEER_INDEPENDENT.json'))
    independent_recovery = independent_peer_interface(independent_reference)
    with tempfile.TemporaryDirectory(prefix='shifted-t72-independent-peer-replay-') as tmp:
        output = Path(tmp)/'peer.json'
        command = [sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])
        proc = subprocess.run(command+[str(independent_script),'--output',str(output)],capture_output=True,text=True)
        need(proc.returncode == 0,'stdlib independent source peer scratch replay '+proc.stderr)
        need(load(output) == independent_reference,'entire independent15-cut peer receipt matches pinned bytes')
    independent_recovery['replayed_into_scratch'] = True
    independent_recovery['receipt_sha256'] = digest(json.dumps(
        {k:v for k,v in independent_reference.items() if k != 'optimized_python'},sort_keys=True).encode())
    mutations = []
    bad = deepcopy(reference)
    bad['frame_contains59'] = True
    mutations.append(reject('silently use frame containing raw59',lambda:source_interface(bad)))
    bad = deepcopy(reference)
    bad['nonnegative_prefix_coordinates'] = 643
    mutations.append(reject('assume full prefix before104 sign recovery',lambda:source_interface(bad)))
    bad = deepcopy(reference)
    bad['nonnegative_support_call_outputs'] = [104,560]
    mutations.append(reject('orient t seed using the unknown104 output',lambda:source_interface(bad)))
    bad = deepcopy(reference)
    bad['actual_calls_interpreted_before825'].append(7)
    mutations.append(reject('interpret call7 before excluding the collapsed shifted-t seed',
        lambda:source_interface(bad)))
    bad = deepcopy(independent_reference)
    bad['exact_t1_identity_without_factorial1_semantics'] = False
    mutations.append(reject('lose the independent t1 identity',lambda:independent_peer_interface(bad)))
    raw = load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    body = load(ROOT/'candidates/projected-radius-mixed-bounds/source/natural667.json')
    restore = load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_restoration.json')
    prior = load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    primitive = module('pinned_independent_raw_compact_inverse',ROOT/'research/paired-index-guard-profile/check.py')
    fixtures = module('pinned_independent_signed_controls',ROOT/'candidates/projected-radius-integers/check.py')
    need([raw['variables'][i] for i in restore['retained_raw_indices']] == body['variables'],
         'all compact body metadata literally selected from the original raw source')
    source_data = load(ROOT/'research/shifted-t-index-guard/CERTIFICATE.json')
    weak_binding = weak_frame_binding(source_data,raw,primitive)
    shifted_binding = shifted_t_binding(source_data,raw,primitive)
    bad = deepcopy(source_data)
    bad['weak_frame_cut']['row_combination'][0]['multiplier'][0][0] += 1
    mutations.append(reject('alter complete weak-frame source ideal',lambda:weak_frame_binding(bad,raw,primitive)))
    bad = deepcopy(source_data)
    bad['early_derived_bounds']['105'] = 2
    mutations.append(reject('assume D>=2 while recovering B sign',lambda:weak_frame_binding(bad,raw,primitive)))
    bad = deepcopy(source_data)
    bad['negative_branch']['seed_recovery_is_conditional'] = False
    mutations.append(reject('claim unconditional paired seed recovery before B sign',
        lambda:weak_frame_binding(bad,raw,primitive)))
    bad = deepcopy(source_data)
    bad['exact_source_cuts']['choose1_digit']['row_combination'][0]['multiplier'][0][0] += 1
    mutations.append(reject('alter the actual choose1 digit source ideal',
        lambda:shifted_t_binding(bad,raw,primitive)))
    bad = deepcopy(source_data)
    bad['chronology']['t1_branch_needs_factorial1_semantics'] = True
    mutations.append(reject('assume g=t! before825 recovery',lambda:shifted_t_binding(bad,raw,primitive)))
    domains,parents = {},{}
    for family in ('compact','raw'):
        old,oldcert = load(predecessor/family/'parent.json'),load(predecessor/family/'domain.json')
        eq,cert = load(HERE/family/'parent.json'),load(HERE/family/'domain.json')
        parents[family] = eq
        initial = prior['prefix_proof']['initial_semantic_guard_indices']
        domains[family] = domain(eq,cert,family,old,oldcert,raw,body,initial)
        bad = deepcopy(eq)
        bad['residuals'][-1]['terms'][1][0] = -1
        mutations.append(reject('weaken actual f-2 predicate '+family,
            lambda:domain(bad,cert,family,old,oldcert,raw,body,initial)))
        bad = deepcopy(cert)
        bad['removed_original_scalar_guard'] = 94
        mutations.append(reject('delete direct remainder sign in place of825 '+family,
            lambda:domain(eq,bad,family,old,oldcert,raw,body,initial)))
        bad = deepcopy(eq)
        bad['variables'][-1]['name'] += '.changed'
        mutations.append(reject('alter surviving predicate auxiliary metadata '+family,
            lambda:domain(bad,cert,family,old,oldcert,raw,body,initial)))
        bad = deepcopy(eq)
        bad['residuals'][0]['terms'][0][0] += 1
        mutations.append(reject('change original body coefficient '+family,
            lambda:domain(bad,cert,family,old,oldcert,raw,body,initial)))
    bridge = primitive.raw_compact_bijection(parents['raw'],parents['compact'],restore,'direct',raw['rows'])
    need(bridge['unique_affine_restorations'] == bridge['forward_monic_uniqueness_rows'] == 592
         and bridge['sign_premises'] == 0,'all592 forward and reverse monic integer restorations')
    archive = REPO/pins['archive']
    need(digest(archive.read_bytes()) == pins['archive_sha256'],'whole independent arithmetic archive')
    census = load(HERE/'CENSUS.json')
    parent_census = load(predecessor/'CENSUS.json')
    need(len(census) == 17 and set(census) == set(parent_census),'same17 settings including raw8/16 default')
    for name,record in census.items():
        need((record['support_cap'],record['affine_cap']) ==
             (parent_census[name]['support_cap'],parent_census[name]['affine_cap']),
             'each support/affine configuration matches frozen73')
    results = {}
    with tempfile.TemporaryDirectory(prefix='shifted-t72-independent-projection-') as tmp,zipfile.ZipFile(archive) as z:
        for name,expected in pins['members'].items():
            need(digest(z.read(name)) == expected,'whole pinned arithmetic member '+name)
        for name in ('verify_projection.py','independent_polynomial.py','audit_common_radix.py'):
            member = next(m for m in pins['members'] if m.endswith('/'+name))
            (Path(tmp)/name).write_bytes(z.read(member))
        sys.path.insert(0,str(tmp))
        from verify_projection import verify
        for name,record in census.items():
            parent = parents[name.split('/')[0]]
            out = load(HERE/name/'equation.json')
            cert = load(HERE/name/'projection.json')
            quartic = load(HERE/name/'polynomial.json')
            need(cert['unconstrained_removed'] == [] and out['metrics'] == record['metrics'] and
                 len(cert['steps']) == record['unique_signed_restorations'],
                 'complete unique-coordinate inverse and freshly measured metric ledger')
            results[name] = dict(projection=verify(parent,out,cert),full_quartic=full_sos(out,quartic),
                arbitrary_signed_restoration_fixtures=fixtures.restoration_controls(parent,out,cert))
            if cert['steps']:
                bad = deepcopy(cert)
                bad['steps'][0]['restoration'][0][0] += 1
                mutations.append(reject('alter signed inverse '+name,lambda:verify(parent,out,bad)))
            bad = deepcopy(quartic)
            bad['terms'][0][0] += 1
            mutations.append(reject('alter complete quartic '+name,lambda:full_sos(out,bad)))
    result = dict(status='PASS',optimized_python=bool(sys.flags.optimize),
        source_guard_recovery=recovery,independent_weak_frame_binding=weak_binding,
        independent_source_peer=independent_recovery,independent_shifted_t_binding=shifted_binding,
        literal_domains=domains,raw_compact_integer_bijection=bridge,
        profiles=results,rejected_corruptions=mutations,optimizer_imported=False,lean_run=False,
        source_pins={str(p.relative_to(ROOT)):digest(p.read_bytes()) for p in
                     (HERE/'README.md',HERE/'ORDINARY_REVIEW.md',HERE/'SOURCE_PINS.json',HERE/'BUILD.json',Path(__file__))},
        scope='Fresh complete72-predicate research systems; exact unrestricted integer inverses before source semantics; separately pinned and replayed641-prefix/43-weak-frame ordinary proof; full quartics. No frontier promotion, optimum, native/internal-ZFC/Lean claim.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',profiles=len(results),corruptions=len(mutations),
        raw_compact_bijection=bridge,modified_prefix_coordinates=641,actual_frame_arguments=43),indent=2))


if __name__ == '__main__':
    main()
