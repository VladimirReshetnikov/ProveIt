#!/usr/bin/env python3
"""Optimizer-free joint-guard common-radius RAW delta, modulus row identity and complete projections."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
import tempfile
import zipfile

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from review_synchronized_certificates import full_sos


def need(ok,why):
    if not ok:raise ValueError(why)


def load(path):return json.loads(path.read_bytes())
def digest(data):return sha256(data).hexdigest()


def sealed(folder):
    manifest=folder/'MANIFEST.json'
    if not manifest.exists():return
    records=load(manifest)['files']
    need(set(records)=={str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p!=manifest},'closed full packet inventory '+str(folder))
    for name,h in records.items():need(digest((folder/name).read_bytes())==h,'whole sealed member '+name)


def literal(original,raw,old,old_domain,parent,domain,cuts,policy):
    need(len(original['variables'])==1259 and len(original['rows'])==1177,'entire frozen594 source inventory')
    need(original['rows'][90]==dict(gate=109,label='multiplication',terms=[[-1,[107,108]],[1,[109]]]),'exact old second radius')
    want=deepcopy(original);want['rows'][90]['terms']=[[-1,[89]],[1,[109]]]
    need(raw==want,'entire source JSON changes only second radius row90')
    need(raw['rows'][75]==dict(gate=89,label='multiplication',terms=[[-1,[87,87]],[1,[89]]]),'first squared radius remains unchanged')
    need(raw['rows'][89]==dict(gate=108,label='multiplication',terms=[[-1,[4,4]],[1,[108]]]),'private t-square row89 retained')
    need([i for i,r in enumerate(raw['rows']) if any(108 in m for c,m in r['terms'])]==[89],'raw108 is retained solely as its private square definition')
    need(old['variables'][:1259]==original['variables'] and old['residuals'][:1177]==[
        dict(label=r['label'],terms=r['terms']) for r in original['rows']],'whole frozen594 source to full parent binding')
    need(len(old['variables'])==1475 and len(old['residuals'])==1249 and len(old_domain['guards'])==72,'entire frozen594 parent shape')
    guards=deepcopy(old_domain['guards'])
    need(guards[71]['predicate']==dict(kind='factorial_index_lower_bound',raw_variables=[87,86],terms=[[1,[87]],[-1,[86]]])
        and guards[71]['auxiliary']==[1472,1473,1474],'exact old final f-K predicate/triple')
    guards[71]['predicate']=dict(kind='factorial_joint_lower_bound',raw_variables=[87,86,107],terms=[[1,[87]],[-1,[86]],[-1,[107]]])
    want=deepcopy(old);want['variant']='common_squared_radius_joint_guard_raw72_literal_prototype'
    want['residuals'][90]['terms']=[[-1,[89]],[1,[109]]]
    want['residuals'][1248]['terms']=[[1,[87]],[-1,[86]],[-1,[107]],[-1,[1472,1472]],[-1,[1473,1473]],[-1,[1474,1474]],[-1,[1474]]]
    need(parent==want,'complete full RAW parent changes only radius row90 and joint guard row1248; all variables unchanged')
    need(domain==dict(baseline_body_variables=1259,baseline_body_rows=1177,baseline_raw_indices=list(range(1259)),
        guards=guards,predicates=72,original_scalar_predicates=69,changed_guard_index=71,
        raw_source='source/raw_builder.json',radius_policy='RADIUS_POLICY.json',
        ordinary_source_equivalence_claimed=False,compact_bridge_assumed=False),'all72 guard records, scalar inventory and metadata exact')
    need(not any(g['predicate'].get('raw_variables')==[825] for g in guards),'raw825 scalar guard has not been restored')
    need(cuts==dict(source_row_map=[[i,i] for i in range(1177)],changed_source_row=90,
        old_source_row=original['rows'][90],new_source_row=raw['rows'][90],parent_row_map=[[i,i] for i in range(1249)],
        changed_parent_rows=[90,1248],guard_index_map=[[i,i] for i in range(72)],changed_guard_index=71,
        old_guard=old_domain['guards'][71],new_guard=guards[71],old_guard_row=old['residuals'][1248],new_guard_row=parent['residuals'][1248],
        variables_unchanged=True,all_other_source_and_parent_records_unchanged=True),'all row/guard maps and changed operands')
    need(policy==dict(schema='literal_common_squared_radius_policy_v2',
        factorial0=dict(input=86,output=87,radius=89,literal_definition='raw89=raw87^2',unchanged=True),
        factorial1=dict(input=4,output=107,radius=109,literal_definition='raw109=raw89',source_row=90),
        retained_private_squares=[dict(variable=88,source_row=74,literal_definition='raw88=raw86^2'),
            dict(variable=108,source_row=89,literal_definition='raw108=raw4^2')],
        changed_predicate=dict(index=71,literal_definition='raw87-raw86-raw107>=0',auxiliary=[1472,1473,1474]),
        raw825_guard_restored=False,duplicated_base_definitions_retained_in_raw=dict(first=92,second=112,first_row=77,second_row=92),
        separate_modulus_alias_bridge='CSE_BRIDGE.json',legacy_raw_metadata_retained_verbatim_except_row90=True,
        metadata_is_not_a_calibration_license=True,
        scope='RAW arithmetic prototype only. No source equivalence, compiler/radix completeness, compact bridge, or accepted metric license. The separate CSE bridge is a universal integer row identity, not a calibration.'),'complete separate common-radius policy and finite boundary')
    return dict(source_rows=1177,parent_rows=1249,guard_predicates=72,unchanged_scalar_predicates=69,
        changed_source_rows=[90],changed_parent_rows=[90,1248],private_t_square108_retained=True,
        raw825_guard_restored=False,all_variables_and_other_records_unchanged=True)


def polynomial(terms):
    out=Counter()
    for c,m in terms:out[tuple(sorted(m))]+=c
    return {m:c for m,c in out.items() if c}


def add(a,b,scale=1):
    out=Counter(a)
    for m,c in b.items():out[m]+=scale*c
    return {m:c for m,c in out.items() if c}


def mul(a,b):
    out=Counter()
    for m,c in a.items():
        for n,d in b.items():out[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in out.items() if c}


def cse_bridge(parent,target,certificate):
    need(len(parent['variables'])==1475 and len(parent['residuals'])==1249,'complete RAW source for row identity')
    want=deepcopy(parent);want['variant']='common_squared_radius_joint_guard_modulus_alias72'
    want['residuals'][711]=dict(label='common_radius.base_modulus_alias',terms=[[1,[764]],[-1,[730]]])
    need(target==want,'whole CSE parent changes exactly row711 and variant; all coordinates and other rows identical')
    q=[[1,[112]],[1,[92]],[-1,[695]]];minusq=[[-c,m] for c,m in q]
    coeffs={str(i):[[c,[]]] for i,c in [(711,-1),(707,1),(708,-1),(709,-1),(710,-1),(673,-1),(674,1),(675,1),(676,1),(677,1)]}
    coeffs.update({'90':minusq,'92':minusq,'77':q})
    need(certificate==dict(schema='common_radius_unit_row_operation_v1',source='raw/parent.json',target='cse/parent.json',
        replaced_row=711,pivot_coefficient=-1,old_row=parent['residuals'][711],new_row=target['residuals'][711],
        identity_coefficients=coeffs,unchanged_rows=[i for i in range(1249) if i!=711],identity_coordinate_bijection=list(range(1475)),
        base_alias_identity=dict(terms=[[1,[112]],[-1,[92]]],row_coefficients={'90':1,'92':1,'77':-1}),
        meaning='new711=sum(coefficients*oldrows); old711=-new711+the unchanged-row sum. Both directions are polynomial identities over unrestricted integers; every other row and coordinate is retained.'),'complete unit row operation certificate and identity coordinate bijection')
    rows=[polynomial(r['terms']) for r in parent['residuals']]
    alias={}
    for i,c in certificate['base_alias_identity']['row_coefficients'].items():alias=add(alias,rows[int(i)],c)
    need(alias==polynomial(certificate['base_alias_identity']['terms']),'universal actual base112-base92 identity')
    combination={};unchanged={}
    for i,p in certificate['identity_coefficients'].items():
        term=mul(polynomial(p),rows[int(i)]);combination=add(combination,term)
        if int(i)!=711:unchanged=add(unchanged,term)
    h=polynomial(target['residuals'][711]['terms'])
    need(combination==h,'unbounded forward modulus-alias row polynomial identity')
    need(add(h,unchanged,-1)=={m:-c for m,c in rows[711].items()},'unbounded inverse row polynomial identity with unit -1 pivot')
    return dict(status='PASS',coordinate_map='identity',coordinates=1475,unchanged_rows=1248,
        replaced_row=711,forward_identity=True,inverse_identity=True,pivot=-1,zero_sets_equal_over='all integers')


def evaluate(terms,values):
    result=0
    for c,m in terms:
        for v in m:c*=values[v]
        result+=c
    return result


def signed_controls(parent,child,certificate):
    for seed in range(3):
        values=[None]*len(parent['variables'])
        for j,v in enumerate(certificate['retained_original_variables']):values[v]=((j+2)*5+seed)%7-3
        for step in reversed(certificate['steps']):
            need(all(values[v] is not None for c,m in step['restoration'] for v in m),'every signed restoration operand already recovered')
            values[step['variable']]=evaluate(step['restoration'],values)
        need(all(v is not None for v in values),'every integer parent coordinate restored')
        reduced=[values[v] for v in certificate['retained_original_variables']]
        for j,rid in enumerate(certificate['retained_original_rows']):
            need(evaluate(parent['residuals'][rid]['terms'],values)==evaluate(child['residuals'][j]['terms'],reduced),'every signed surviving row agrees')
        removed=set(range(len(parent['residuals'])))-set(certificate['retained_original_rows'])
        need(all(evaluate(parent['residuals'][rid]['terms'],values)==0 for rid in removed),'every removed defining/zero residual restored')
    return 3


def complete_quartic(out,quartic):
    measured=full_sos(out,quartic)
    measured['max_abs_row_coefficient']=max(abs(c) for row in out['residuals'] for c,m in row['terms'])
    measured['variable_kinds']=dict(Counter(v['kind'] for v in out['variables']))
    need(out['metrics']==measured,'every actual census field independently remeasured')
    return measured


def reject(name,action):
    try:action()
    except (ValueError,RuntimeError,KeyError,TypeError,IndexError):return name
    raise ValueError('corruption accepted '+name)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    sealed(HERE)
    pins=load(HERE/'SOURCE_PINS.json')
    need(pins['ordinary_source_equivalence_claimed'] is False and pins['compact_bridge_assumed'] is False,'research-only scope in immutable inputs')
    for name,h in pins['files'].items():need(digest((ROOT/name).read_bytes())==h,'whole immutable input '+name)
    baseline=ROOT/pins['parent_profile'];sealed(baseline)
    build=load(HERE/'BUILD.json')
    need(build['generator_sha256']==digest((HERE/'build.py').read_bytes()) and build['source_pins_sha256']==digest((HERE/'SOURCE_PINS.json').read_bytes()),'producer and complete source pins')
    for name,h in build['files'].items():need(digest((HERE/name).read_bytes())==h,'whole generated equation/restoration/quartic '+name)
    original=load(baseline/'source/raw_builder.json');raw=load(HERE/'source/raw_builder.json')
    old=load(baseline/'raw/parent.json');old_domain=load(baseline/'raw/domain.json')
    parent=load(HERE/'raw/parent.json');domain=load(HERE/'raw/domain.json');cuts=load(HERE/'CUTS.json');policy=load(HERE/'RADIUS_POLICY.json')
    inputs=(original,raw,old,old_domain,parent,domain,cuts,policy)
    binding=literal(*inputs)
    target=load(HERE/'cse/parent.json');bridge=load(HERE/'CSE_BRIDGE.json');bridge_result=cse_bridge(parent,target,bridge)
    mutations=[]
    def changed(position,mutation):
        values=list(inputs);values[position]=deepcopy(values[position]);mutation(values[position]);return lambda:literal(*values)
    mutations.append(reject('retain old g*t^2 radius',changed(1,lambda x:x['rows'][90].update(terms=original['rows'][90]['terms']))))
    mutations.append(reject('delete private t-square wire definition',changed(1,lambda x:x['rows'][89].update(terms=[[-1,[87,87]],[1,[108]]]))))
    mutations.append(reject('weaken joint guard back to f-K',changed(4,lambda x:x['residuals'][1248].update(terms=old['residuals'][1248]['terms']))))
    mutations.append(reject('alter unrelated source row',changed(4,lambda x:x['residuals'][0]['terms'][0].__setitem__(0,-2))))
    mutations.append(reject('change final guard auxiliary metadata',changed(4,lambda x:x['variables'][1474].update(name='altered auxiliary'))))
    mutations.append(reject('claim ordinary source equivalence',changed(5,lambda x:x.update(ordinary_source_equivalence_claimed=True))))
    mutations.append(reject('claim compact bridge',changed(5,lambda x:x.update(compact_bridge_assumed=True))))
    mutations.append(reject('lose guard row map',changed(6,lambda x:x['guard_index_map'].__setitem__(71,[71,70]))))
    mutations.append(reject('claim raw825 guard restored',changed(7,lambda x:x.update(raw825_guard_restored=True))))
    mutations.append(reject('license calibration from inherited headers',changed(7,lambda x:x.update(metadata_is_not_a_calibration_license=False))))
    bad=deepcopy(bridge);bad['identity_coefficients']['707'][0][0]+=1
    mutations.append(reject('alter universal modulus identity coefficient',lambda:cse_bridge(parent,target,bad)))
    bad_target=deepcopy(target);bad_target['residuals'][711]['terms'][0][1]=[765]
    mutations.append(reject('alias wrong modulus coordinate',lambda:cse_bridge(parent,bad_target,bridge)))
    bad_bridge=deepcopy(bridge);bad_bridge['pivot_coefficient']=1
    mutations.append(reject('lose invertible minus-one row pivot',lambda:cse_bridge(parent,target,bad_bridge)))
    bad_target=deepcopy(target);bad_target['residuals'][707]['terms'][0][0]=-2
    mutations.append(reject('change an allegedly unchanged CSE row',lambda:cse_bridge(parent,bad_target,bridge)))
    configurations=[('retained',0,None),('support2_affine1',2,1),('support2_affine2',2,2),('support4_affine2',4,2),
        ('support8_affine2',8,2),('support16_affine2',16,2),('support32_affine2',32,2),
        ('support8_affine3',8,3),('support16_affine3',16,3),('support32_affine3',32,3),
        ('support8_default',8,None),('support16_default',16,None)]
    settings={mode+'/'+name:(cap,affine) for mode in ['raw','cse'] for name,cap,affine in configurations}
    census=load(HERE/'CENSUS.json');need(set(census)==set(settings),'all24 RAW and separately bridged CSE configurations')
    old_census=load(baseline/'CENSUS.json');comparison=[]
    for name,record in sorted(census.items()):
        previous='raw/'+name.split('/')[1];a,b=old_census[previous]['metrics'],record['metrics']
        comparison.append(dict(configuration=name,frozen594_configuration=previous,old_literal_metrics=a,new_prototype_metrics=b,
            delta={k:b[k]-a[k] for k in ['variables','quadratic_rows','expanded_monomials','max_abs_expanded_coefficient']},ordinary_source_equivalence_claimed=False))
    need(load(HERE/'MEASURED_COMPARISON.json')==dict(scope='Measured arithmetic prototypes only; no common-radius source calibration or accepted metric license.',comparisons=comparison),'all measured same-setting differences without semantic license')
    need(not (HERE/'compact').exists(),'no compact equation or assumed bridge')
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole reviewed monic projection archive')
    results={}
    with tempfile.TemporaryDirectory(prefix='common-squared-radius-independent-') as tmp,zipfile.ZipFile(archive) as z:
        for name,h in pins['members'].items():need(digest(z.read(name))==h,'whole reviewed archive member '+name)
        for filename in ['verify_projection.py','independent_polynomial.py','audit_common_radix.py']:
            member=next(n for n in pins['members'] if n.endswith('/'+filename));(Path(tmp)/filename).write_bytes(z.read(member))
        sys.path.insert(0,str(tmp))
        from verify_projection import verify
        for name,record in census.items():
            need((record['support_cap'],record['affine_cap'])==settings[name] and record['ordinary_source_equivalence_claimed'] is False,'exact optimizer settings and finite status')
            full=parent if name.startswith('raw/') else target
            out=load(HERE/name/'equation.json');cert=load(HERE/name/'projection.json');quartic=load(HERE/name/'polynomial.json')
            need(cert['unconstrained_removed']==record['unconstrained_removed']==[] and len(cert['steps'])==record['unique_signed_restorations'] and out['metrics']==record['metrics'],'complete restoration and census ledger')
            results[name]=dict(projection=verify(full,out,cert),full_quartic=complete_quartic(out,quartic),signed_fixture_count=signed_controls(full,out,cert))
            if cert['steps']:
                bad_cert=deepcopy(cert);bad_cert['steps'][0]['restoration'][0][0]+=1
                mutations.append(reject('alter signed inverse '+name,lambda:verify(full,out,bad_cert)))
            bad_poly=deepcopy(quartic);bad_poly['terms'][0][0]+=1
            mutations.append(reject('alter full quartic coefficient '+name,lambda:complete_quartic(out,bad_poly)))
            bad_out=deepcopy(out);bad_out['metrics']['max_abs_row_coefficient']+=1
            mutations.append(reject('alter measured row height '+name,lambda:complete_quartic(bad_out,quartic)))
        need(not any('terminal_elimination' in k or 'monic_engine' in k for k in sys.modules),'optimizer not imported by separate checker')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),literal_raw_binding=binding,cse_integer_bridge=bridge_result,
        profiles=results,rejected_corruptions=mutations,optimizer_imported=False,compact_bridge_assumed=False,
        ordinary_source_equivalence_claimed=False,accepted_metrics_promoted=False,lean_run=False,
        source_pins={name:digest((HERE/name).read_bytes()) for name in ['README.md','FEASIBILITY.md','SOURCE_PINS.json','BUILD.json','RADIUS_POLICY.json','CUTS.json','CSE_BRIDGE.json','MEASURED_COMPARISON.json','check.py']},
        scope='Exact common-radius RAW/joint-guard delta, all-integer invertible CSE row identity, complete unrestricted-integer monic projections and quartics only. No ordinary compiler/radix/source calibration or accepted metric license.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',profiles=len(results),corruptions=len(mutations),ordinary_source_equivalence_claimed=False),sort_keys=True))


if __name__=='__main__':main()
