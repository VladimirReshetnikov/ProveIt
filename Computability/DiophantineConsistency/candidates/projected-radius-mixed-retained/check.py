#!/usr/bin/env python3
"""Independent raw bounds, literal994 bridge, private ledger and signed inverses."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
NAMES = ['retained', 'support2_affine1', 'support2_affine2', 'support4_affine2', 'support8_affine2']
sys.path.insert(0, str(ROOT / 'tools'))
from review_quartics407888 import raw_export
from review_synchronized_certificates import full_sos


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(name):
    return json.loads((HERE / name).read_text())


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def digest(raw):
    return sha256(raw).hexdigest()


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec); spec.loader.exec_module(result)
    return result


def bound_step(source, step, known, b):
    v, lower = step['variable'], step['lower']
    factor, rhs = b.poly(step['factor']), b.poly(step['rhs'])
    need(type(v) is int and 0 <= v < 1259 and v not in known
         and type(lower) is int and lower >= 1, 'fresh strictly positive bound')
    need(all(0 <= i < 1259 and i != v for p in [factor, rhs] for m in p for i in m), 'bound target independent')
    expected = b.add(b.mul({(v,): 1}, factor), rhs, -1)
    actual = {}
    for item in step['row_combination']:
        need(0 <= item['row'] < 1177, 'original raw ideal row')
        multiplier = b.poly(item['multiplier'])
        need(all(0 <= i < 1259 for m in multiplier for i in m), 'integer ideal multiplier coordinates')
        actual = b.add(actual, b.mul(multiplier, b.poly(source['residuals'][item['row']]['terms'])))
    need(actual == expected, 'entire original-row ideal identity')
    pf = b.nonnegative(factor, known, True)
    pg = b.nonnegative(b.add(rhs, factor, -(lower-1)), known, True)
    known[v] = lower
    return dict(variable=v, lower=lower, shifted_factor=[[c, list(m)] for m, c in sorted(pf.items())],
                shifted_gap=[[c, list(m)] for m, c in sorted(pg.items())])


def domain(source, signed, cert, route, route_sign, b, mixed):
    ids = {encoded(v): i for i, v in enumerate(source['variables'])}
    need(len(ids) == 1259, 'unique complete raw identities')
    mapped = {ids[encoded(route['variables'][v])] for v in route_sign['guards']}
    omitted = {ids[encoded(route['variables'][v])] for v in route_sign['removed_guards']}
    seeds = cert['seed_indices']
    need(cert['mapped_route_guard_indices'] == sorted(mapped)
         and seeds == sorted(mapped - {644, 917}) and len(seeds) == 107,
         'raw107 seeds are exact mapped109 minus the two proved signs')
    need(cert['omitted_quotient_indices'] == sorted(omitted) and len(omitted) == 52
         and cert['omitted_bound_indices'] == [644, 917], 'complete omitted roles')
    need(signed['domain'] == 'unrestricted integers' and signed['variables'][:1259] == source['variables']
         and signed['residuals'][:1177] == source['residuals'], 'every original raw coefficient retained')
    need(len(signed['variables']) == 1580 and len(signed['residuals']) == 1284, 'full raw mixed dimensions')
    need([g['variable'] for g in cert['guards']] == seeds, 'all107 guard slots')
    for j, g in enumerate(cert['guards']):
        a, bb, c = range(1259+3*j, 1262+3*j); v = g['variable']
        need(g['auxiliary'] == [a, bb, c] and b.poly(signed['residuals'][1177+j]['terms'])
             == {(v,): 1, (a,a): -1, (bb,bb): -1, (c,): -1, (c,c): -1}, 'entire private guard row')
    known_bounds = {v: 0 for v in seeds}
    bounds = [bound_step(source, s, known_bounds, b) for s in cert['bound_steps']]
    need([(s['variable'], s['lower']) for s in bounds] == [(4,1),(5,2),(644,2),(917,2)], 'four ordered strict bounds')
    known = set(known_bounds)
    for step in cert['sign_steps']:
        mixed.inferred_step(source, step, known)
    need(len(cert['sign_steps']) == 976 and len(known) == 1087
         and cert['known_after_initial_steps'] == sorted(known), 'fresh complete976-step sign boundary')
    parts = cert['unresolved']
    groups = [set(parts[k]) for k in ['quotients', 'comparison_coordinates', 'private_gates']]
    need([len(g) for g in groups] == [52,30,90]
         and all(not(a & c) for j,a in enumerate(groups) for c in groups[:j])
         and set.union(*groups) == set(range(1259))-known, 'entire172-coordinate signed/private remainder')
    need(groups[0] == omitted, 'signed quotient remainder has checked macro roles')
    need(all(re.fullmatch(r'index\d+\.(S|R)', source['variables'][i]['name']) for i in groups[1])
         and all(source['variables'][i]['kind']=='gate' for i in groups[2]), 'exact comparison/gate remainder categories')
    # Do not infer B's sign from B=A+U*bq while bq is signed.
    for v in known:
        known_bounds.setdefault(v, 0)
    base_bound = bound_step(source, cert['early_comparison_base_bound'], known_bounds, b)
    need(base_bound['variable'] == 667 and base_bound['lower'] == 1, 'independent early B defining-gate bound')
    known.add(667)
    before_index = set(known)
    late = set(cert['late_semantic_quotients'])
    byname = {v['name']: i for i,v in enumerate(source['variables'])}
    need(late == {byname['shared_index.Bquotient']} | {byname['pow'+str(j)+'.quotient'] for j in range(21)},
         'only22 separately proved orientations admitted later')
    known.update(late)
    for step in cert['late_sign_steps']:
        mixed.inferred_step(source, step, known)
    need(len(cert['late_sign_steps']) == 29 and len(known) == 1139
         and cert['known_after_late_orientations'] == sorted(known), 'full later private sign boundary')
    return dict(seed_count=107, original_sign_steps=976, initially_nonnegative=1087,
                early_base_bound=base_bound, shifted_bound_steps=bounds,
                nonnegative_before_signed_index=len(before_index), late_orientation_results=22,
                late_existing_sign_steps=29, later_nonnegative=1139), before_index


def bridge994(source, signed, route, route_sign, foundation, cert, bridge, mixed):
    ids = {encoded(v): i for i,v in enumerate(source['variables'])}
    retained = [ids[encoded(v)] for v in route['variables']]
    need(bridge['retained_raw_indices'] == retained and retained == sorted(set(retained)), 'complete raw-to667 coordinate map')
    mixed.guard_equation(route, foundation, route_sign)  # literal target994 rows/guards, not an abstract relation
    mapped = {retained[v] for v in route_sign['guards']}
    need(bridge['mapped_994_guard_indices'] == sorted(mapped)
         and bridge['raw107_guard_indices'] == cert['seed_indices']
         and bridge['replaced_raw_guard_indices'] == [644,917], 'exact107+2 guard transfer')
    reverse = {v:i for i,v in enumerate(retained)}
    positions = {v:j for j,v in enumerate(route_sign['guards'])}
    need(len(bridge['shared_guard_transfers']) == 107, 'every old107 guard witness copied')
    for j, item in enumerate(bridge['shared_guard_transfers']):
        v = cert['seed_indices'][j]; cv = reverse[v]
        need(item == dict(raw_variable=v, contracted_variable=cv,
            source_auxiliary=cert['guards'][j]['auxiliary'],
            target_auxiliary=list(range(667+3*positions[cv],670+3*positions[cv]))),
            'exact raw/contracted value and three-square witness positions')
    new = bridge['new_994_guard_triples']
    need([s['raw_variable'] for s in new] == [644,917], 'only A,D require fresh two guard witnesses')
    for item in new:
        v = item['raw_variable']; cv = reverse[v]
        need(item == dict(raw_variable=v, contracted_variable=cv,
            target_auxiliary=list(range(667+3*positions[cv],670+3*positions[cv]))), 'exact A,D target guard slots')
    need(bridge['contracted_bound_replacements'] == [dict(contracted_variable=i, raw_variable=v)
        for i,v in enumerate(retained) if v in {644,917}], 'both bound targets are actual retained coordinates')
    return dict(raw_coordinates=1259, contracted_coordinates=667, restored_affine_coordinates=592,
                copied_guard_triples=107, derived_nonnegative_guard_values=2,
                fresh_existential_guard_witnesses=6, literal_target_integer_variables=994,
                scope='All restoration is over Z. Legendre supplies only the two derived guard triples; the sealed994 theorem supplies signed-index/positive-comparison normalization.')


def privacy(raw, interface, known):
    names={v['name']:i for i,v in enumerate(raw['variables'])}
    rows={r['label']:i for i,r in enumerate(raw['rows'])if r.get('gate')is None}
    need(len(names)==1259,'unique complete raw role names')
    need(interface['private_start'] == 643 and interface['semantic_prefix_raw_variables'] == list(range(643))
         and set(range(643)) <= known, 'entire actual semantic prefix natural')
    need(interface['nonnegative_raw_before_index_recovery'] == sorted(known), 'complete current raw sign ledger')
    gates = [i for i,r in enumerate(raw['rows']) if r.get('gate') is not None]
    semantic = [i for i,r in enumerate(raw['rows']) if r.get('gate') is None
                and all(v<643 for c,m in r['terms'] for v in m)]
    private = [i for i,r in enumerate(raw['rows']) if r.get('gate') is None and i not in semantic]
    need(interface['all_gate_rows'] == gates and interface['semantic_non_gate_rows'] == semantic
         and interface['private_non_gate_rows'] == private and (len(gates),len(semantic),len(private)) == (1029,39,109),
         'fresh complete1177-row privacy partition')
    definitions = {r['gate'] for r in raw['rows'] if r.get('gate') is not None}
    free = sorted(set(range(643,1259))-definitions)
    need(interface['private_free_variables'] == free and len(free) == 142, 'all actual private free inputs')
    expected_free={names[n]for n in ['shared.W','shared.A','shared.Zminus1','shared_index.U',
        'shared_index.V','shared_index.q4minus1','shared_index.Bquotient',
        'shared_index.Vquotient_minus1','index_addition.D']}
    expected_rows={rows[n]for n in ['shared.last_norm','shared.frame_definition','shared_index.norm',
        'shared_index.B_mod_U','shared_index.V_positive_product','index_addition.D_definition']}
    need(interface['frame'] == raw['scale'] and interface['auxiliary'] == raw['auxiliary']
         and interface['all_indices'] == raw['indices'] and interface['derivations'] == raw['derivations'], 'all shared/index references')
    need(len(interface['seeds']) == len(raw['seeds']) == 15 and len(interface['powers']) == len(raw['powers']) == 21,
         'every seed and every power call retained')
    for x,y in zip(interface['seeds'],raw['seeds']):
        need(x['exponent']==y['exponent'] and [x['X'],x['Y']]==y['pair'], 'actual seed binding')
        need(all(x[k][1] in known for k in ['X','Y','YminusK']), 'main seed domains proved before signed-index use')
        prefix=raw['variables'][x['X'][1]]['name'].removesuffix('.X')
        for k in ['X','Y','S','R','YminusK','Squotient','Rquotient']:
            need(x[k]==['v',names[prefix+'.'+k]],'all seed coordinate roles bound to literal inputs')
            expected_free.add(x[k][1])
        for k in ['index_at_most_Y','norm1','norm3','S_mod_U','R_mod_4Y']:
            need(x['rows'][k]==rows[prefix+'.'+k],'all seed residual slots')
            expected_rows.add(x['rows'][k])
    for j,(x,y) in enumerate(zip(interface['powers'],raw['powers'])):
        need(all(x[k]==y[k] and x[k][1]<643 and x[k][1] in known for k in ['base','exponent','output']),
             'no private input in any semantic power argument/output')
        need(x['quotient']==['v',names['pow'+str(j)+'.quotient']]
             and x['row']==rows['pow'+str(j)+'.power_congruence'],'complete actual power quotient/row roles')
        expected_free.add(x['quotient'][1]);expected_rows.add(x['row'])
    for n,i in names.items():
        if re.fullmatch(r'base\d+\.T',n):
            need(i in known,'all actual natural moduli')
            expected_free.add(i);expected_rows.add(rows[n.removesuffix('.T')+'.T_definition'])
    need(set(free)==expected_free and set(private)==expected_rows,'complete reconstruction roles for every private input and constraint')
    need(all(t[1] in known for t in raw['scale']+raw['auxiliary']), 'all shared coordinates natural independently')
    return dict(semantic_prefix=643, semantic_constraints=39, private_constraints=109,
                private_free_inputs=142, gate_definitions=1029, powers=21, seeds=15, derived_pairs=1)


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('--output',type=Path); args=parser.parse_args()
    pins=load('SOURCE_PINS.json')
    for n,pin in pins['sources'].items():
        data=(HERE/'source'/n).read_bytes()
        need(digest(data)==pin['sha256'] and data==(ROOT/pin['repository_path']).read_bytes(), 'complete frozen input '+n)
    four=pins['four_bound_source']; need(digest((ROOT/four['repository_path']).read_bytes())==four['sha256'], 'immutable four-bound source')
    need(load('source/four_bounds.json')==json.loads((ROOT/four['repository_path']).read_text())['bound_steps'], 'all four original bound certificates')
    for n,h in pins['independent_helpers'].items(): need(digest((ROOT/n).read_bytes())==h,'independent helper '+n)
    for n,h in pins['ordinary_proof_dependencies'].items(): need(digest((ROOT/n).read_bytes())==h,'ordinary dependency '+n)
    build=load('BUILD.json'); need(digest((HERE/'build.py').read_bytes())==build['generator_sha256'],'generator pin')
    for n,h in build['sha256'].items(): need(digest((HERE/n).read_bytes())==h,'entire generated artifact '+n)
    source=load('source/raw_natural.json'); raw=load('source/raw_builder.json'); route=load('source/route_natural667.json'); route_sign=load('source/route_sign.json')
    need(source['variables']==raw['variables'] and source['residuals']==[dict(label=r['label'],terms=r['terms'])for r in raw['rows']], 'exact full1259/1177 raw source')
    signed=load('guarded.json'); cert=load('domain_certificate.json')
    b=module('frozen_shifted_bound_checker',ROOT/'candidates/retained-radius-bounds/check.py')
    mixed=module('frozen_mixed994_checker',ROOT/'candidates/projected-radius-mixed/check.py')
    signs,known=domain(source,signed,cert,route,route_sign,b,mixed)
    foundation_dir=ROOT/pins['mixed994_foundation']['directory']
    for n,h in pins['mixed994_foundation']['files'].items(): need(digest((foundation_dir/n).read_bytes())==h,'sealed994 foundation '+n)
    for n,h in json.loads((foundation_dir/'MANIFEST.json').read_text())['files'].items():
        need(digest((foundation_dir/n).read_bytes())==h,'complete sealed994 member '+n)
    bridge=bridge994(source,signed,route,route_sign,json.loads((foundation_dir/'equation.json').read_text()),cert,load('BRIDGE994.json'),mixed)
    mixed.restoration(raw,route,load('source/route_raw_restoration.json'),set())  # integer identities only
    export=raw_export(raw,load('source/gate_ledger.json'),route)
    interface=load('arithmetic_interfaces.json'); boundary=privacy(raw,interface,known)
    normalization=mixed.comparison_normalization(load('COMPARISON_NORMALIZATION.json'))
    theorem=pins['signed_theorem_archive'];need(digest((REPO/theorem['repository_path']).read_bytes())==theorem['sha256'], 'whole inherited signed-index theorem archive')
    archive=REPO/pins['arithmetic_archive']; need(digest(archive.read_bytes())==pins['arithmetic_archive_sha256'],'whole frozen arithmetic archive')
    results={}; mutations=[]
    def reject(label,thunk):
        try: thunk()
        except(ValueError,RuntimeError,KeyError,IndexError,TypeError): mutations.append(label)
        else: raise ValueError('corruption accepted '+label)
    with tempfile.TemporaryDirectory(prefix='raw107-independent-')as tmp,zipfile.ZipFile(archive)as z:
        code=Path(tmp)
        for member,h in pins['arithmetic_source_members'].items():
            data=z.read(member); need(digest(data)==h,'exact arithmetic member')
            if Path(member).name!='terminal_elimination.py': (code/Path(member).name).write_bytes(data)
        arithmetic=module('frozen_raw_scalar_auditor',code/'audit_new.py')
        scalar_module=module('frozen_actual_scalar_interfaces',ROOT/'candidates/projected-factorial-radius/check.py')
        class TracedAudit(arithmetic.Audit):
            touched=set()
            def row_poly(self,label,leaves,disc=False):
                self.touched.add(label)
                return super().row_poly(label,leaves,disc)
        scalar=scalar_module.scalar_audit(raw,TracedAudit)
        audit=TracedAudit(raw); A=raw['scale'][1][1]; D=raw['discriminant'][1]
        ap,dp={(-1,):1},{(-2,):1}
        need(audit.row_poly('index_addition.D_definition',{A:ap,D:dp})
             == b.add(b.add(b.mul(ap,ap),dp,-1),{():1},-1),'entire actual discriminant row')
        need({raw['rows'][i]['label']for i in interface['private_non_gate_rows']}<=TracedAudit.touched,
             'every private constraint covered by exact scalar identities')
        sys.path.insert(0,str(code)); from verify_projection import verify
        inverse=module('frozen_independent_inverse_controls',ROOT/'candidates/projected-radius-integers/check.py')
        for name in NAMES:
            child=load(name+'/equation.json'); projection=load(name+'/elimination_certificate.json')
            need(projection['unconstrained_removed']==[],'entire mixed raw parent restored')
            results[name]=dict(restoration=verify(signed,child,projection),metrics=full_sos(child,load(name+'/expanded_polynomial.json')),
                               signed_restoration_controls=inverse.restoration_controls(signed,child,projection))
            if projection['steps']:
                bad=deepcopy(projection); bad['steps'][0]['restoration'][0][0]+=1
                reject('changed signed inverse '+name,lambda:verify(signed,child,bad))
        bad=deepcopy(cert);bad['bound_steps'][2]['row_combination'][4]['multiplier']=[[-1,[]]]
        reject('changed nonconstant ideal multiplier',lambda:domain(source,signed,bad,route,route_sign,b,mixed))
        bad=deepcopy(cert);bad['bound_steps'][1]['lower']=1
        reject('only n>=1 for A bound',lambda:domain(source,signed,bad,route,route_sign,b,mixed))
        bad=deepcopy(cert);bad['bound_steps'][2]['lower']=3
        reject('unsupported A>=3',lambda:domain(source,signed,bad,route,route_sign,b,mixed))
        bad=deepcopy(cert);bad['sign_steps'][0]['rhs'][0][0]+=1
        reject('changed actual raw sign identity',lambda:domain(source,signed,bad,route,route_sign,b,mixed))
        bad=load('BRIDGE994.json');bad['shared_guard_transfers'][0]['target_auxiliary'][0]+=1
        reject('wrong literal994 guard witness slot',lambda:bridge994(source,signed,route,route_sign,json.loads((foundation_dir/'equation.json').read_text()),cert,bad,mixed))
        bad=deepcopy(interface);bad['private_free_variables'].pop()
        reject('missing private free input',lambda:privacy(raw,bad,known))
        bad=load('support8_affine2/expanded_polynomial.json');bad['terms'][0][0]+=1
        reject('changed entire quartic coefficient',lambda:full_sos(load('support8_affine2/equation.json'),bad))
    command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[])+[str(foundation_dir/'check.py')]
    proc=subprocess.run(command,capture_output=True,text=True);need(proc.returncode==0,'frozen994 checker '+proc.stderr)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),domain=signs,literal994_bridge=bridge,
        complete_integer_raw_export=export,private_dataflow=boundary,scalar_interfaces=scalar,
        explicit_comparison_lift=normalization,variants=results,rejected_corruptions=mutations,
        foundation994=dict(status='PASS',stdout_sha256=digest(proc.stdout.encode())),
        scope='All original raw coefficients retained; reverse integer maps precede107 guards/strict bounds and the literal994 existential bridge. Fresh sign/privacy ledger is supplemental, not a pointwise all-natural claim. No Lean.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output: args.output.write_text(text)
    print(text,end='')


if __name__=='__main__': main()
