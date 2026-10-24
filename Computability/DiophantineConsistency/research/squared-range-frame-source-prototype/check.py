#!/usr/bin/env python3
"""Optimizer-free eight-square frame,64 predicates, exact row bridge and complete quartics."""
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


OUTPUTS=[573,583,591,599,607,617,625,635]
QUOTIENTS=[575,584,592,600,609,618,627,636]
FRAME_ROWS=[1165,1167,1168,1169,1170,1172,1173,1175]


def literal(original,raw,old,old_domain,parent,domain,cuts,policy,radius):
    need((len(original['variables']),len(original['rows']),len(old['variables']),len(old['residuals']))==(1259,1177,1475,1249),'complete frozen591 source and RAW parent')
    need(old['variables'][:1259]==original['variables'] and old['residuals'][:1177]==[
        dict(label=r['label'],terms=r['terms']) for r in original['rows']],'complete original source-parent binding')
    want=deepcopy(original);newvars=list(range(1259,1267));newrows=list(range(1177,1185))
    for output,var,rowid in zip(OUTPUTS,newvars,FRAME_ROWS):
        want['variables'].append(dict(kind='gate',name='frame.range_output_square.'+str(output)))
        want['rows'].append(dict(gate=var,label='frame_range_output_square',terms=[[-1,[output,output]],[1,[var]]]))
        need(want['rows'][rowid]['terms'].count([-1,[output]])==1,'one original frame output coefficient')
        want['rows'][rowid]['terms']=[[-1,[var]] if t==[-1,[output]] else t for t in want['rows'][rowid]['terms']]
    need(raw==want,'entire source JSON changes only eight frame summands plus eight appended square definitions; all old metadata preserved')
    retained=[];removed=[];guards=[];variables=deepcopy(raw['variables']);residuals=[dict(label=r['label'],terms=r['terms']) for r in raw['rows']]
    variable_map={i:i for i in range(1259)};guard_map=[];row_map=[[i,i] for i in range(1177)]
    for i,g in enumerate(old_domain['guards']):
        if g['predicate'].get('raw_variables') in [[q] for q in QUOTIENTS]:
            need(g['predicate']['kind']=='retained_scalar','removed graph is exactly an original scalar quotient predicate')
            removed.append(i);guard_map.append([i,None]);row_map.append([1177+i,None]);continue
        j=len(guards);retained.append(i);guard_map.append([i,j]);row_map.append([1177+i,1185+j])
        fresh=deepcopy(g);fresh['auxiliary']=list(range(len(variables),len(variables)+3))
        for a,b in zip(g['auxiliary'],fresh['auxiliary']):variable_map[a]=b;variables.append(deepcopy(old['variables'][a]))
        guards.append(fresh);remap=dict(zip(g['auxiliary'],fresh['auxiliary']))
        residuals.append(dict(label=old['residuals'][1177+i]['label'],terms=[[c,[remap.get(v,v) for v in m]] for c,m in old['residuals'][1177+i]['terms']]))
    want=deepcopy(old);want.update(variant='squared_range_output_frame64_raw_literal_prototype',variables=variables,residuals=residuals)
    need(parent==want,'entire parent, all eight square rows, every retained guard graph/attribute and auxiliary reindexing exact')
    need(len(removed)==8 and len(guards)==64 and len(variables)==1459 and len(residuals)==1249 and
        len([g for g in guards if g['predicate']['kind']=='retained_scalar'])==61,'exact61 scalar plus three combined predicates;24 old auxiliaries removed and8 source squares appended')
    need(domain==dict(baseline_body_variables=1267,baseline_body_rows=1185,baseline_raw_indices=list(range(1267)),
        guards=guards,predicates=64,original_scalar_predicates=61,removed_quotient_variables=QUOTIENTS,
        raw_source='source/raw_builder.json',frame_policy='FRAME_POLICY.json',radius_policy='RADIUS_POLICY.json',
        ordinary_source_equivalence_claimed=False,compact_bridge_assumed=False),'all64 guard records and exact domain scope')
    need(cuts==dict(original_source_row_map=[[i,i] for i in range(1177)],changed_source_rows=FRAME_ROWS,
        appended_square_rows=newrows,appended_square_variables=newvars,
        old_frame_rows={str(i):original['rows'][i] for i in FRAME_ROWS},new_frame_rows={str(i):raw['rows'][i] for i in FRAME_ROWS},
        parent_row_map=row_map,guard_index_map=guard_map,removed_guard_indices=removed,retained_guard_indices=retained,
        retained_old_variable_map=[[i,variable_map[i]] for i in sorted(variable_map)],
        removed_old_variables=sorted(set(range(1475))-set(variable_map)),all_other_original_source_rows_unchanged=True),'complete source,parent,guard and retained/removed variable maps')
    ports=sorted({a[1] for call in original['powers'] for a in call.values()});squaremap=dict(zip(OUTPUTS,newvars))
    need(len(ports)==43 and len(original['powers'])==21,'all actual power request ports retained')
    need(policy==dict(schema='eight_squared_range_output_frame_v1',actual_power_ports=ports,bounding_ports=[squaremap.get(v,v) for v in ports],
        replaced_outputs=OUTPUTS,square_variables=newvars,square_rows=newrows,changed_frame_rows=FRAME_ROWS,
        removed_quotient_guards=QUOTIENTS,actual_power_requests_unchanged=True,
        all_other_original_source_metadata_and_records_unchanged=True,appended_squares_need_no_input_signs=True,
        original_numeric_gate_order_is_not_a_chronological_premise=True,
        old_frame_calibration_not_assumed=True,ordinary_source_equivalence_claimed=False,
        scope='Eight-only RAW arithmetic prototype. Squared bounding ports replace only the eight possibly signed range outputs in W. Ordinary source/semantics/completeness are separate; no accepted metric license.'),'entire explicit frame policy; no inherited frame license')
    joint=next(i for i,g in enumerate(guards) if g['predicate']['kind']=='factorial_joint_lower_bound')
    need(joint==63 and radius==dict(schema='inherited_common_squared_radius_v1',
        factorial0=dict(input=86,output=87,radius=89,literal_definition='raw89=raw87^2'),
        factorial1=dict(input=4,output=107,radius=109,literal_definition='raw109=raw89'),
        private_squares=[dict(variable=88,row=74,literal_definition='raw88=raw86^2'),dict(variable=108,row=89,literal_definition='raw108=raw4^2')],
        unchanged_radius_rows=[75,90],joint_guard=dict(index=joint,predicate=guards[joint]['predicate'],auxiliary=guards[joint]['auxiliary']),
        ordinary_source_equivalence_claimed=False),'unchanged common radii and exact retained joint guard after reindexing')
    return dict(source_variables=1267,source_rows=1185,parent_variables=1459,parent_rows=1249,
        guard_predicates=64,scalar_predicates=61,removed_quotient_variables=QUOTIENTS,
        changed_source_rows=FRAME_ROWS,appended_square_rows=newrows,actual_power_ports_unchanged=True,
        old_frame_calibration_assumed=False)

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
    need(len(parent['variables'])==1459 and len(parent['residuals'])==1249,'complete RAW source for row identity')
    want=deepcopy(parent);want['variant']='squared_range_output_frame64_modulus_alias'
    want['residuals'][711]=dict(label='common_radius.base_modulus_alias',terms=[[1,[764]],[-1,[730]]])
    need(target==want,'whole CSE parent changes exactly row711 and variant; all coordinates and other rows identical')
    q=[[1,[112]],[1,[92]],[-1,[695]]];minusq=[[-c,m] for c,m in q]
    coeffs={str(i):[[c,[]]] for i,c in [(711,-1),(707,1),(708,-1),(709,-1),(710,-1),(673,-1),(674,1),(675,1),(676,1),(677,1)]}
    coeffs.update({'90':minusq,'92':minusq,'77':q})
    need(certificate==dict(schema='common_radius_unit_row_operation_v1',source='raw/parent.json',target='cse/parent.json',
        replaced_row=711,pivot_coefficient=-1,old_row=parent['residuals'][711],new_row=target['residuals'][711],
        identity_coefficients=coeffs,unchanged_rows=[i for i in range(1249) if i!=711],identity_coordinate_bijection=list(range(1459)),
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
    return dict(status='PASS',coordinate_map='identity',coordinates=1459,unchanged_rows=1248,
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
    squaremap=dict(zip(OUTPUTS,range(1259,1267)))
    frame=[[1,[643]],[-2,[]]]+[[-1,[v,v] if v in OUTPUTS else [v]] for v in ports]
    weak=[[1,[643]],[-1,[105]]]+[[-1,[v,v] if v in OUTPUTS else [v]] for v in ports if v!=104]
    rows=[dict(multiplier=[[1,[]]],row=47)]+[dict(multiplier=[[1,[]]],row=i) for i in range(1134,1185)]
    cuts=dict(frame=dict(polynomial=frame,row_combination=rows),
        weak=dict(polynomial=weak,row_combination=rows[:1]+[dict(multiplier=[[-1,[]]],row=88)]+rows[1:]))
    need(certificate==dict(schema='eight_squared_frame_complete_ideals_v1',actual_power_ports=ports,
        square_map=[[v,squaremap[v]] for v in OUTPUTS],cuts=cuts,
        scope='Exact polynomial identities over all integers. The ordinary absolute-value frame and source semantics are separately proved.'),'complete ordinary/weak frame coefficient ledgers')
    for name,cut in cuts.items():
        result={}
        for item in cut['row_combination']:result=add(result,mul(polynomial(item['multiplier']),polynomial(raw['rows'][item['row']]['terms'])))
        need(result==polynomial(cut['polynomial']),'unbounded actual '+name+' squared-frame identity')
    return dict(status='PASS',ordinary_identity=True,weak_identity=True,actual_power_ports=43,squared_output_ports=8,zero_input_sign_premises=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    sealed(HERE)
    pins=load(HERE/'SOURCE_PINS.json')
    need(pins['ordinary_source_equivalence_claimed'] is False and pins['compact_bridge_assumed'] is False,'research-only immutable input boundary')
    for name,h in pins['files'].items():need(digest((ROOT/name).read_bytes())==h,'whole immutable input '+name)
    baseline=ROOT/pins['parent_profile'];sealed(baseline)
    build=load(HERE/'BUILD.json')
    need(build['generator_sha256']==digest((HERE/'build.py').read_bytes()) and build['source_pins_sha256']==digest((HERE/'SOURCE_PINS.json').read_bytes()),'producer and complete input pins')
    for name,h in build['files'].items():need(digest((HERE/name).read_bytes())==h,'whole generated equation/restoration/quartic '+name)
    original=load(baseline/'source/raw_builder.json');raw=load(HERE/'source/raw_builder.json')
    old=load(baseline/'raw/parent.json');old_domain=load(baseline/'raw/domain.json')
    parent=load(HERE/'raw/parent.json');domain=load(HERE/'raw/domain.json');cuts=load(HERE/'CUTS.json');policy=load(HERE/'FRAME_POLICY.json');radius=load(HERE/'RADIUS_POLICY.json')
    inputs=(original,raw,old,old_domain,parent,domain,cuts,policy,radius)
    binding=literal(*inputs);frame_certificate=load(HERE/'FRAME_IDENTITIES.json');frame_result=frame_identities(raw,frame_certificate)
    target=load(HERE/'cse/parent.json');bridge=load(HERE/'CSE_BRIDGE.json');bridge_result=cse_bridge(parent,target,bridge)
    mutations=[]
    def changed(position,mutation):
        values=list(inputs);values[position]=deepcopy(values[position]);mutation(values[position]);return lambda:literal(*values)
    mutations.append(reject('retain old linear range-output frame port',changed(1,lambda x:x['rows'].__setitem__(1165,original['rows'][1165]))))
    mutations.append(reject('square the wrong range-output coordinate',changed(1,lambda x:x['rows'][1177].update(terms=[[-1,[574,574]],[1,[1259]]]))))
    mutations.append(reject('bind actual power output to its square',changed(1,lambda x:x['powers'][10].update(output=['v',1259]))))
    mutations.append(reject('alter unrelated native row',changed(1,lambda x:x['rows'][0]['terms'][0].__setitem__(0,-2))))
    mutations.append(reject('retain a deleted quotient guard',changed(5,lambda x:x['guards'].append(old_domain['guards'][34]))))
    mutations.append(reject('claim ordinary source equivalence',changed(5,lambda x:x.update(ordinary_source_equivalence_claimed=True))))
    mutations.append(reject('claim compact bridge',changed(5,lambda x:x.update(compact_bridge_assumed=True))))
    mutations.append(reject('change retained guard auxiliary metadata',changed(4,lambda x:x['variables'][-1].update(name='altered auxiliary'))))
    mutations.append(reject('lose removed-variable map',changed(6,lambda x:x['removed_old_variables'].pop())))
    mutations.append(reject('substitute old frame calibration',changed(7,lambda x:x.update(old_frame_calibration_not_assumed=False))))
    mutations.append(reject('weaken retained joint factorial guard',changed(8,lambda x:x['joint_guard']['predicate'].update(terms=[[1,[87]],[-1,[86]]]))))
    bad_frame=deepcopy(frame_certificate);bad_frame['cuts']['weak']['row_combination'][1]['multiplier']=[[1,[]]]
    mutations.append(reject('wrong weak frame cancellation sign',lambda:frame_identities(raw,bad_frame)))
    bad_frame2=deepcopy(frame_certificate);bad_frame2['cuts']['frame']['polynomial'][1][0]=-1
    mutations.append(reject('alter complete frame constant',lambda:frame_identities(raw,bad_frame2)))
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
        comparison.append(dict(configuration=name,frozen591_configuration=previous,old_literal_metrics=a,new_prototype_metrics=b,
            delta={k:b[k]-a[k] for k in ['variables','quadratic_rows','expanded_monomials','max_abs_expanded_coefficient']},ordinary_source_equivalence_claimed=False))
    need(load(HERE/'MEASURED_COMPARISON.json')==dict(scope='Measured eight-only squared-frame arithmetic prototypes; no source calibration or accepted metric license.',comparisons=comparison),'all measured same-setting differences without semantic license')
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
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),literal_raw_binding=binding,frame_integer_identities=frame_result,cse_integer_bridge=bridge_result,
        profiles=results,rejected_corruptions=mutations,optimizer_imported=False,compact_bridge_assumed=False,
        ordinary_source_equivalence_claimed=False,accepted_metrics_promoted=False,lean_run=False,
        source_pins={name:digest((HERE/name).read_bytes()) for name in ['README.md','FEASIBILITY.md','SOURCE_PINS.json','BUILD.json','RADIUS_POLICY.json','FRAME_POLICY.json','FRAME_IDENTITIES.json','CUTS.json','CSE_BRIDGE.json','MEASURED_COMPARISON.json','check.py']},
        scope='Exact eight-output squared-frame/64-guard RAW delta, full integer frame identities, invertible CSE row identity and complete signed monic projections/quartics only. No ordinary compiler/radix/source calibration or accepted metric license.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',profiles=len(results),corruptions=len(mutations),ordinary_source_equivalence_claimed=False),sort_keys=True))


if __name__=='__main__':main()
