#!/usr/bin/env python3
"""Optimizer-free raw6-only existing-square frame,63 predicates and complete integer quartics."""
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


RANGE_OUTPUTS=[573,583,591,599,607,617,625,635]
SQUARED_OUTPUTS=[6]+RANGE_OUTPUTS


def literal(original,raw,old,old_domain,parent,domain,cuts,policy,radius,previous_policy,previous_radius):
    need((len(original['variables']),len(original['rows']),len(old['variables']),len(old['residuals']))==(1267,1185,1459,1249),'complete frozen575 RAW source and parent')
    need(old['variables'][:1267]==original['variables'] and old['residuals'][:1185]==[
        dict(label=r['label'],terms=r['terms']) for r in original['rows']],'whole source-parent binding')
    want=deepcopy(original);need(want['rows'][1135]['terms'].count([-1,[6]])==1,'one actual power0 frame occurrence')
    want['rows'][1135]['terms']=[[-1,[7]] if t==[-1,[6]] else t for t in want['rows'][1135]['terms']]
    need(raw==want,'whole source changes only row1135 port6 to existing7; all variables and metadata unchanged')
    need(raw['rows'][2]==dict(gate=7,label='multiplication',terms=[[-1,[6,6]],[1,[7]]]),'actual existing raw7 square definition')
    need([i for i,r in enumerate(raw['rows']) if any(6 in m for c,m in r['terms'])]==[2,649],'complete actual source occurrences of raw6 after frame change')
    retained=[];removed=[];guards=[];variables=deepcopy(raw['variables']);residuals=[dict(label=r['label'],terms=r['terms']) for r in raw['rows']]
    variable_map={i:i for i in range(1267)};guard_map=[];row_map=[[i,i] for i in range(1185)]
    for i,g in enumerate(old_domain['guards']):
        if g['predicate'].get('raw_variables')==[6]:
            need(g['predicate']['kind']=='retained_scalar','only scalar6 graph is removed')
            removed.append(i);guard_map.append([i,None]);row_map.append([1185+i,None]);continue
        j=len(guards);retained.append(i);guard_map.append([i,j]);row_map.append([1185+i,1185+j])
        fresh=deepcopy(g);fresh['auxiliary']=list(range(len(variables),len(variables)+3))
        for a,b in zip(g['auxiliary'],fresh['auxiliary']):variable_map[a]=b;variables.append(deepcopy(old['variables'][a]))
        guards.append(fresh);remap=dict(zip(g['auxiliary'],fresh['auxiliary']))
        residuals.append(dict(label=old['residuals'][1185+i]['label'],terms=[[c,[remap.get(v,v) for v in m]] for c,m in old['residuals'][1185+i]['terms']]))
    want=deepcopy(old);want.update(variant='power0_existing_square_frame63_raw_literal_prototype',variables=variables,residuals=residuals)
    need(parent==want,'complete new parent and every retained graph/name/attribute/reindexing exact')
    need(removed==[2] and len(guards)==63 and len(variables)==1456 and len(residuals)==1248 and
        sum(g['predicate']['kind']=='retained_scalar' for g in guards)==60,'exactly one scalar triple removed; no new source variable')
    need(any(g['predicate']==dict(kind='retained_scalar',raw_variables=[106],terms=[[1,[106]]]) for g in guards),'the raw106 scalar guard remains intact')
    absent=old_domain['removed_quotient_variables']
    need(domain==dict(baseline_body_variables=1267,baseline_body_rows=1185,baseline_raw_indices=list(range(1267)),
        guards=guards,predicates=63,original_scalar_predicates=60,newly_removed_scalar_variables=[6],inherited_absent_quotient_variables=absent,
        raw_source='source/raw_builder.json',frame_policy='FRAME_POLICY.json',radius_policy='RADIUS_POLICY.json',
        ordinary_source_equivalence_claimed=False,compact_bridge_assumed=False),'all63 guard records and exact scope')
    need(cuts==dict(original_source_row_map=[[i,i] for i in range(1185)],changed_source_rows=[1135],
        old_frame_row=original['rows'][1135],new_frame_row=raw['rows'][1135],source_variables_unchanged=True,
        parent_row_map=row_map,guard_index_map=guard_map,removed_guard_indices=removed,retained_guard_indices=retained,
        retained_old_variable_map=[[i,variable_map[i]] for i in sorted(variable_map)],removed_old_variables=sorted(set(range(1459))-set(variable_map)),
        all_other_original_source_rows_unchanged=True),'all original rows,retained/removed guard maps and auxiliary coordinate maps')
    ports=previous_policy['actual_power_ports']
    need(ports==sorted({a[1] for call in raw['powers'] for a in call.values()}) and len(ports)==43,'same21 actual power requests and43 ports')
    need(policy==dict(schema='power0_existing_square_frame63_v1',actual_power_ports=ports,
        bounding_ports=[7 if v==6 else b for v,b in zip(ports,previous_policy['bounding_ports'])],
        newly_squared_output=dict(output=6,square_variable=7,source_square_row=2,changed_frame_row=1135,gate_already_present=True),
        inherited_range_square_outputs=previous_policy['replaced_outputs'],inherited_square_variables=previous_policy['square_variables'],inherited_square_rows=previous_policy['square_rows'],
        newly_removed_scalar_guard=6,raw106_guard_retained=True,inherited_absent_quotient_guards=absent,
        actual_power_requests_unchanged=True,all_other_original_source_records_unchanged=True,
        old_frame_calibration_not_assumed=True,ordinary_source_equivalence_claimed=False,
        scope='Raw6-only RAW arithmetic prototype. Existing raw7=raw6^2 replaces only frame port6; all eight earlier range squares remain. Ordinary helper/power/source/completeness proof is separate; no accepted metric license.'),'entire explicit source/frame policy without inherited calibration')
    joint=next(i for i,g in enumerate(guards) if g['predicate']['kind']=='factorial_joint_lower_bound')
    expected_radius=deepcopy(previous_radius);expected_radius['joint_guard']=dict(index=joint,predicate=guards[joint]['predicate'],auxiliary=guards[joint]['auxiliary'])
    need(joint==62 and radius==expected_radius,'all radius laws retained with exact joint guard auxiliary reindexing only')
    return dict(source_variables=1267,source_rows=1185,parent_variables=1456,parent_rows=1248,
        guard_predicates=63,scalar_predicates=60,newly_removed_scalar=6,raw106_guard_retained=True,
        changed_source_rows=[1135],new_source_variables=0,actual_power_ports_unchanged=True,old_frame_calibration_assumed=False)

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
    need(len(parent['variables'])==1456 and len(parent['residuals'])==1248,'complete RAW source for row identity')
    want=deepcopy(parent);want['variant']='power0_existing_square_frame63_modulus_alias'
    want['residuals'][711]=dict(label='common_radius.base_modulus_alias',terms=[[1,[764]],[-1,[730]]])
    need(target==want,'whole CSE parent changes exactly row711 and variant; all coordinates and other rows identical')
    q=[[1,[112]],[1,[92]],[-1,[695]]];minusq=[[-c,m] for c,m in q]
    coeffs={str(i):[[c,[]]] for i,c in [(711,-1),(707,1),(708,-1),(709,-1),(710,-1),(673,-1),(674,1),(675,1),(676,1),(677,1)]}
    coeffs.update({'90':minusq,'92':minusq,'77':q})
    need(certificate==dict(schema='common_radius_unit_row_operation_v1',source='raw/parent.json',target='cse/parent.json',
        replaced_row=711,pivot_coefficient=-1,old_row=parent['residuals'][711],new_row=target['residuals'][711],
        identity_coefficients=coeffs,unchanged_rows=[i for i in range(1248) if i!=711],identity_coordinate_bijection=list(range(1456)),
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
    return dict(status='PASS',coordinate_map='identity',coordinates=1456,unchanged_rows=1247,
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

def frame_identities(raw,certificate):
    ports=sorted({a[1] for call in raw['powers'] for a in call.values()})
    squaremap={6:7,**dict(zip(RANGE_OUTPUTS,range(1259,1267)))}
    frame=[[1,[643]],[-2,[]]]+[[-1,[v,v] if v in SQUARED_OUTPUTS else [v]] for v in ports]
    weak=[[1,[643]],[-1,[105]]]+[[-1,[v,v] if v in SQUARED_OUTPUTS else [v]] for v in ports if v!=104]
    rows=[dict(multiplier=[[1,[]]],row=2),dict(multiplier=[[1,[]]],row=47)]+[dict(multiplier=[[1,[]]],row=i) for i in range(1134,1185)]
    cuts=dict(frame=dict(polynomial=frame,row_combination=rows),
        weak=dict(polynomial=weak,row_combination=rows[:2]+[dict(multiplier=[[-1,[]]],row=88)]+rows[2:]))
    need(certificate==dict(schema='power0_and_eight_squared_frame_complete_ideals_v1',actual_power_ports=ports,
        square_map=[[v,squaremap[v]] for v in SQUARED_OUTPUTS],cuts=cuts,
        scope='Exact polynomial identities over all integers. The ordinary absolute-value frame and source semantics are separately proved.'),'complete ordinary/weak frame coefficient ledgers')
    for name,cut in cuts.items():
        result={}
        for item in cut['row_combination']:result=add(result,mul(polynomial(item['multiplier']),polynomial(raw['rows'][item['row']]['terms'])))
        need(result==polynomial(cut['polynomial']),'unbounded actual '+name+' squared-frame identity')
    return dict(status='PASS',ordinary_identity=True,weak_identity=True,actual_power_ports=43,squared_output_ports=9,zero_input_sign_premises=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    sealed(HERE)
    pins=load(HERE/'SOURCE_PINS.json')
    need(pins['ordinary_source_equivalence_claimed'] is False and pins['compact_bridge_assumed'] is False,'research-only immutable input boundary')
    for name,h in pins['files'].items():need(digest((ROOT/name).read_bytes())==h,'whole immutable input '+name)
    baseline=ROOT/pins['parent_profile'];sealed(baseline)
    ordinary=ROOT/pins['ordinary_packet'];sealed(ordinary)
    need(digest((ordinary/'MANIFEST.json').read_bytes())==pins['ordinary_manifest_sha256']=='0797e4244ae0c65ed2fecffebcc6445bfda60729714fc973e32fee716db48d75','exact separately sealed ordinary63 source proof')
    build=load(HERE/'BUILD.json')
    need(build['generator_sha256']==digest((HERE/'build.py').read_bytes()) and build['source_pins_sha256']==digest((HERE/'SOURCE_PINS.json').read_bytes()),'producer and complete input pins')
    for name,h in build['files'].items():need(digest((HERE/name).read_bytes())==h,'whole generated equation/restoration/quartic '+name)
    original=load(baseline/'source/raw_builder.json');raw=load(HERE/'source/raw_builder.json')
    old=load(baseline/'raw/parent.json');old_domain=load(baseline/'raw/domain.json')
    parent=load(HERE/'raw/parent.json');domain=load(HERE/'raw/domain.json');cuts=load(HERE/'CUTS.json');policy=load(HERE/'FRAME_POLICY.json');radius=load(HERE/'RADIUS_POLICY.json')
    previous_policy=load(baseline/'FRAME_POLICY.json');previous_radius=load(baseline/'RADIUS_POLICY.json')
    inputs=(original,raw,old,old_domain,parent,domain,cuts,policy,radius,previous_policy,previous_radius)
    binding=literal(*inputs);frame_certificate=load(HERE/'FRAME_IDENTITIES.json');frame_result=frame_identities(raw,frame_certificate)
    target=load(HERE/'cse/parent.json');bridge=load(HERE/'CSE_BRIDGE.json');bridge_result=cse_bridge(parent,target,bridge)
    mutations=[]
    def changed(position,mutation):
        values=list(inputs);values[position]=deepcopy(values[position]);mutation(values[position]);return lambda:literal(*values)
    mutations.append(reject('retain old linear power0 frame port',changed(1,lambda x:x['rows'].__setitem__(1135,original['rows'][1135]))))
    mutations.append(reject('change the existing power0 square gate',changed(1,lambda x:x['rows'][2].update(terms=[[-1,[5,5]],[1,[7]]]))))
    mutations.append(reject('bind actual power0 output to its square',changed(1,lambda x:x['powers'][0].update(output=['v',7]))))
    mutations.append(reject('alter an inherited squared range frame',changed(1,lambda x:x['rows'][1165]['terms'].__setitem__(1,[-1,[573]]))))
    mutations.append(reject('alter unrelated native row',changed(1,lambda x:x['rows'][0]['terms'][0].__setitem__(0,-2))))
    mutations.append(reject('restore removed raw6 guard',changed(5,lambda x:x['guards'].append(old_domain['guards'][2]))))
    mutations.append(reject('remove retained raw106 guard',changed(5,lambda x:x['guards'].__delitem__(next(i for i,g in enumerate(x['guards']) if g['predicate'].get('raw_variables')==[106])))))
    mutations.append(reject('claim ordinary source equivalence',changed(5,lambda x:x.update(ordinary_source_equivalence_claimed=True))))
    mutations.append(reject('claim compact bridge',changed(5,lambda x:x.update(compact_bridge_assumed=True))))
    mutations.append(reject('change retained guard auxiliary metadata',changed(4,lambda x:x['variables'][-1].update(name='altered auxiliary'))))
    mutations.append(reject('lose removed-variable map',changed(6,lambda x:x['removed_old_variables'].pop())))
    mutations.append(reject('substitute old frame calibration',changed(7,lambda x:x.update(old_frame_calibration_not_assumed=False))))
    mutations.append(reject('weaken retained joint factorial guard',changed(8,lambda x:x['joint_guard']['predicate'].update(terms=[[1,[87]],[-1,[86]]]))))
    bad_frame=deepcopy(frame_certificate);bad_frame['cuts']['weak']['row_combination'][2]['multiplier']=[[1,[]]]
    mutations.append(reject('wrong weak frame cancellation sign',lambda:frame_identities(raw,bad_frame)))
    bad_frame2=deepcopy(frame_certificate);bad_frame2['cuts']['frame']['polynomial'][1][0]=-1
    mutations.append(reject('alter complete frame constant',lambda:frame_identities(raw,bad_frame2)))
    bad_frame3=deepcopy(frame_certificate);bad_frame3['cuts']['frame']['row_combination'].pop(0)
    mutations.append(reject('omit existing raw7 square identity',lambda:frame_identities(raw,bad_frame3)))
    bad_bridge=deepcopy(bridge);bad_bridge['identity_coefficients']['707'][0][0]+=1
    mutations.append(reject('alter universal modulus identity coefficient',lambda:cse_bridge(parent,target,bad_bridge)))
    bad_target=deepcopy(target);bad_target['residuals'][711]['terms'][0][1]=[765]
    mutations.append(reject('alias wrong modulus coordinate',lambda:cse_bridge(parent,bad_target,bridge)))
    bad_bridge2=deepcopy(bridge);bad_bridge2['pivot_coefficient']=1
    mutations.append(reject('lose invertible minus-one row pivot',lambda:cse_bridge(parent,target,bad_bridge2)))
    configurations=[('retained',0,None),('support2_affine1',2,1),('support2_affine2',2,2),('support4_affine2',4,2),
        ('support8_affine2',8,2),('support16_affine2',16,2),('support32_affine2',32,2),
        ('support8_affine3',8,3),('support16_affine3',16,3),('support32_affine3',32,3),
        ('support8_default',8,None),('support16_default',16,None)]
    settings={mode+'/'+name:(cap,affine) for mode in ['raw','cse'] for name,cap,affine in configurations}
    census=load(HERE/'CENSUS.json');need(set(census)==set(settings),'all24 RAW and separately bridged CSE configurations')
    old_census=load(baseline/'CENSUS.json');comparison=[]
    for name,record in sorted(census.items()):
        previous=name;a,b=old_census[previous]['metrics'],record['metrics']
        comparison.append(dict(configuration=name,frozen575_configuration=previous,old_literal_metrics=a,new_prototype_metrics=b,
            delta={k:b[k]-a[k] for k in ['variables','quadratic_rows','expanded_monomials','max_abs_expanded_coefficient']},ordinary_source_equivalence_claimed=False))
    need(load(HERE/'MEASURED_COMPARISON.json')==dict(scope='Measured raw6-only existing-square-frame arithmetic prototypes; no source calibration or accepted metric license.',comparisons=comparison),'all measured same-setting differences without semantic license')
    need(not (HERE/'compact').exists(),'no compact equation or assumed bridge')
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole reviewed monic projection archive')
    results={}
    with tempfile.TemporaryDirectory(prefix='power0-square-frame-independent-') as tmp,zipfile.ZipFile(archive) as z:
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
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),literal_raw_binding=binding,frame_integer_identities=frame_result,cse_integer_bridge=bridge_result,
        profiles=results,rejected_corruptions=mutations,optimizer_imported=False,compact_bridge_assumed=False,
        ordinary_source_equivalence_claimed=False,accepted_metrics_promoted=False,lean_run=False,
        source_pins={name:digest((HERE/name).read_bytes()) for name in ['README.md','FEASIBILITY.md','SOURCE_PINS.json','BUILD.json','RADIUS_POLICY.json','FRAME_POLICY.json','FRAME_IDENTITIES.json','CUTS.json','CSE_BRIDGE.json','MEASURED_COMPARISON.json','check.py']},
        scope='Exact raw6-only existing-square-frame/63-guard RAW delta, full integer frame identities, invertible CSE row identity and complete signed monic projections/quartics only. No ordinary compiler/radix/source calibration or accepted metric license.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',profiles=len(results),corruptions=len(mutations),ordinary_source_equivalence_claimed=False),sort_keys=True))


if __name__=='__main__':main()
