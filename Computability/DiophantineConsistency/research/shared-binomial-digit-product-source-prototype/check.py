#!/usr/bin/env python3
"""Optimizer-free binomial product55 RAW/CSE equations and complete quartics."""
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


def P(terms):
    out={}
    for c,m in terms:
        need(type(c) is int and all(type(v) is int for v in m),'complete integer polynomial terms')
        k=tuple(sorted(m));out[k]=out.get(k,0)+c
    return {m:c for m,c in out.items() if c}
def add(a,b,scale=1):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+scale*c
    return {m:c for m,c in out.items() if c}
def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return {m:c for m,c in out.items() if c}
def guard_binding(values,old):
    raw,parent,domain,frame,radius,certificate,cuts=values
    oldraw,oldparent,olddomain,oldframe,oldradius=old
    need(raw==oldraw and frame==oldframe,'ENTIRE body/frame/ports/metadata unchanged')
    need((len(raw['variables']),len(raw['rows']),len(oldparent['variables']),len(oldparent['residuals']),len(olddomain['guards']))==(1268,1186,1436,1242,56),'whole frozen56 boundary')
    need(oldparent['variables'][:1268]==raw['variables'] and oldparent['residuals'][:1186]==[dict(label=r['label'],terms=r['terms']) for r in raw['rows']],'every body variable/row exact')
    singles={g['predicate']['raw_variables'][0]:i for i,g in enumerate(olddomain['guards']) if g['predicate']['kind']=='retained_scalar'}
    need([singles[v] for v in [123,564,94,95,537]]==[17,30,12,13,23] and 91 not in singles,'actual two removed signs, three retained source signs,91 not directly guarded')
    ledgers=[('derived_anchor',[[1,[91]],[-1,[94]],[-1,[95]],[-1,[]]],[(83,1),(84,1),(85,1)]),('anchor_digit',[[1,[530]],[-1,[91]],[-1,[537]],[-1,[]]],[(518,1),(519,1),(520,1)]),('target_digit',[[1,[530]],[-1,[123]],[-1,[564]],[-1,[]]],[(540,1),(541,1),(542,1)]),('anchored_difference',[[1,[123]],[1,[564]],[-1,[91]],[-1,[537]]],[(518,1),(519,1),(520,1),(540,-1),(541,-1),(542,-1)])]
    identities={}
    for label,target,combination in ledgers:
        total={}
        for i,c in combination:total=add(total,mul(P([[c,[]]]),P(raw['rows'][i]['terms'])))
        need(total==P(target),'all coefficients of actual body ideal '+label)
        identities[label]=dict(polynomial=target,row_combination=[dict(row=i,multiplier=[[c,[]]]) for i,c in combination])
    names=deepcopy(raw['variables']);rows=deepcopy(oldparent['residuals'][:1186]);guards=[];vmap={i:i for i in range(1268)};rmap=[[i,i] for i in range(1186)];gmap=[];kept=[]
    for i,g in enumerate(olddomain['guards']):
        if i==30:gmap.append(dict(old_index=i,new_index=17,kind='replaced_pair_member'));continue
        j=len(guards);aux=[1268+3*j,1269+3*j,1270+3*j]
        if i==17:
            label='shared_binomial_digit_product.123.564';a,b,c=aux;names.extend(dict(kind='nonnegative_guard',name=label+'.'+s) for s in ['a','b','c'])
            predicate=dict(kind='shared_binomial_digit_product',raw_variables=[123,564],terms=[[1,[123,564]]]);row=dict(label=label,terms=[[1,[123,564]],[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]);gmap.append(dict(old_index=i,new_index=j,kind='replaced_pair_member'))
        else:
            predicate=deepcopy(g['predicate']);remap=dict(zip(g['auxiliary'],aux))
            for a,b in zip(g['auxiliary'],aux):vmap[a]=b;names.append(deepcopy(oldparent['variables'][a]))
            row=dict(label=oldparent['residuals'][1186+i]['label'],terms=[[c,[remap.get(v,v) for v in m]] for c,m in oldparent['residuals'][1186+i]['terms']]);rmap.append([1186+i,1186+j]);kept.append(i);gmap.append(dict(old_index=i,new_index=j,kind='retained'))
        guards.append(dict(auxiliary=aux,predicate=predicate));rows.append(row)
    wanted=deepcopy(oldparent);wanted.update(variant='shared_binomial_digit_product_guard55_raw_literal',variables=names,residuals=rows)
    need(parent==wanted and (len(names),len(rows),len(guards))==(1433,1241,55),'EVERY new row/variable/label/attribute, all unchanged body and surviving guards')
    need(all(i in kept for i in [12,13,23]),'all three source-anchor signs retained before any interpretation')
    kinds={k:sum(g['predicate']['kind']==k for g in guards) for k in ['retained_scalar','shared_remainder_product','shared_binomial_digit_product']}
    need(kinds==dict(retained_scalar=45,shared_remainder_product=6,shared_binomial_digit_product=1),'all45scalar,6inheritedproducts,1newproduct and3inheritedreplacements')
    for j,(g,row) in enumerate(zip(guards,rows[1186:])):
        a,b,c=g['auxiliary'];need(g['auxiliary']==list(range(1268+3*j,1271+3*j)) and P(row['terms'])==add(P(g['predicate']['terms']),P([[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]])),'every55 complete Legendre quadratic and contiguous auxiliary triple')
    wantdomain=deepcopy(olddomain);wantdomain.update(guards=guards,predicates=55,original_scalar_predicates=45,shared_binomial_digit_product_predicates=1,replaced_scalar_pairs=olddomain['replaced_scalar_pairs']+[[123,564]],binomial_digit_anchor=[91,537],derived_anchor_source=[94,95])
    need(domain==wantdomain,'ENTIRE domain and source/predicate/port policies')
    wantradius=deepcopy(oldradius);wantradius['joint_guard']=dict(index=54,predicate=guards[54]['predicate'],auxiliary=guards[54]['auxiliary'])
    need(radius==wantradius and guards[54]['auxiliary']==[1430,1431,1432],'all radius laws unchanged, only joint guard mapping shifts')
    wantcuts=dict(source_row_map=[[i,i] for i in range(1186)],source_variables_unchanged=True,source_rows_unchanged=True,retained_parent_rows=rmap,guard_index_map=gmap,retained_old_guard_indices=kept,replaced_guard_indices=[17,30],retained_old_variable_map=[[i,vmap[i]] for i in sorted(vmap)],removed_old_auxiliary=sorted(set(range(1436))-set(vmap)),new_product_auxiliary=guards[17]['auxiliary'],auxiliary_zero_sets_identified_pointwise=False,raw_coordinate_projection='identity',quantification='For each unrestricted integer tuple satisfying the unchanged1186 body residuals, existence of old56guard witnesses iff existence of new55guard witnesses.')
    need(cuts==wantcuts and cuts['removed_old_auxiliary']==[1319,1320,1321,1358,1359,1360] and cuts['new_product_auxiliary']==[1319,1320,1321],'complete integer raw/retainedaux/row/guard maps; numeric auxiliary overlap is not identification')
    wantcert=dict(schema='shared_binomial_digit_product_guard_equivalence_v1',body_variables=1268,body_rows=1186,old_parent_variables=1436,old_parent_rows=1242,old_predicates=56,new_parent_variables=1433,new_parent_rows=1241,new_predicates=55,retained_scalars=45,inherited_remainder_products=6,new_product_predicates=1,preserved_replacement_predicates=3,pair=[123,564],anchor=[91,537],derived_anchor=91,direct_anchor_source=[94,95,537],direct_anchor_guard_indices=[12,13,23],old_guard_indices=[17,30],old_auxiliary_groups=[olddomain['guards'][i]['auxiliary'] for i in [17,30]],old_guard_rows=[1203,1216],new_guard_index=17,new_auxiliary=guards[17]['auxiliary'],new_parent_row=1203,source_identities=identities,legendre_graph=dict(polynomial='u-a^2-b^2-c^2-c',auxiliary_domain='all integers',represented_values='all nonnegative integers'),raw_body_byte_unchanged=True,all_power_and_frame_ports_unchanged=True,all_old_signs_restored_before_parent_semantics=True,direct_guard_on_91_assumed=False,denominator_or_pell_meaning_used=False,ordinary_equivalence_proof='PROOF.md',projected_metrics_claimed=False,new_lean_claim=False)
    need(certificate==wantcert,'every body ideal coefficient, derived anchor, operand/old-new graph and scope certificate')
    return dict(status='PASS',body_coordinates=1268,body_rows=1186,old_parent_coordinates=1436,new_parent_coordinates=1433,old_parent_rows=1242,new_parent_rows=1241,predicates=55,retained_scalars=45,inherited_remainder_products=6,new_product_predicates=1,preserved_replacement_predicates=3,collected_source_identities=4,identity_labels=list(identities),complete_legendre_graphs=55,direct_anchor_scalar_graphs=3,derived_anchor_lower_bound=1,removed_old_auxiliary=6,new_product_auxiliary=3,whole_raw_projection='identity',whole_guarded_tuple_bijection_claimed=False,power_or_frame_meaning_used=False)

RANGE_OUTPUTS=[573,583,591,599,607,617,625,635]
SQUARED_OUTPUTS=[6,106]+RANGE_OUTPUTS
polynomial=P


def literal(original,raw,old,old_domain,parent,domain,cuts,frame,radius,previous_frame,previous_radius,certificate,guard_policy):
    result=guard_binding([raw,parent,domain,frame,radius,certificate,cuts],[original,old,old_domain,previous_frame,previous_radius])
    copied=['source/raw_builder.json','raw/parent.json','raw/domain.json','FRAME_POLICY.json','RADIUS_POLICY.json','CUTS.json','CERTIFICATE.json','PROOF.md','BOUNDARY.md']
    want=dict(schema='shared_binomial_digit_product_guard55_finite_binding_v1',ordinary_packet='research/shared-binomial-digit-product-guard',ordinary_manifest_sha256='14d504be627beaba1caf9c5f704da6762bfd693a1416a84f1bedf9d9df7197f0',copied_ordinary_files=copied,arithmetic_body_unchanged_from_baseline=True,raw_parent_and_domain_byte_identical_to_ordinary=True,new_body_gates=0,replaced_scalar_pair=certificate['pair'],anchor=certificate['anchor'],derived_anchor=certificate['derived_anchor'],retained_anchor_source=certificate['direct_anchor_source'],body_coordinates=1268,body_rows=1186,predicates=55,retained_scalar_predicates=45,inherited_remainder_products=6,new_product_predicates=1,preserved_replacement_predicates=3,raw_body_projection='identity',guard_auxiliaries_reconstructed_existentially=True,whole_guarded_tuple_bijection_assumed=False,ordinary_source_equivalence_claimed=False,compact_bridge_assumed=False,accepted_metrics_promoted=False,scope='Finite complete RAW/CSE algebra/projection/quartic candidate. Ordinary same-body guard-domain equivalence comes only from the separately sealed ordinary packet. No projected count is inferred from guard removal.')
    need(guard_policy==want,'complete accepted ordinary license and finite-only guard policy')
    return result


def cse_bridge(parent,target,certificate):
    need(len(parent['variables'])==1433 and len(parent['residuals'])==1241,'complete RAW source for row identity')
    want=deepcopy(parent);want['variant']='shared_binomial_digit_product_guard55_modulus_alias'
    want['residuals'][711]=dict(label='common_radius.base_modulus_alias',terms=[[1,[764]],[-1,[730]]])
    need(target==want,'whole CSE parent changes exactly row711 and variant; all coordinates and other rows identical')
    q=[[1,[112]],[1,[92]],[-1,[695]]];minusq=[[-c,m] for c,m in q]
    coeffs={str(i):[[c,[]]] for i,c in [(711,-1),(707,1),(708,-1),(709,-1),(710,-1),(673,-1),(674,1),(675,1),(676,1),(677,1)]}
    coeffs.update({'90':minusq,'92':minusq,'77':q})
    need(certificate==dict(schema='common_radius_unit_row_operation_v1',source='raw/parent.json',target='cse/parent.json',
        replaced_row=711,pivot_coefficient=-1,old_row=parent['residuals'][711],new_row=target['residuals'][711],
        identity_coefficients=coeffs,unchanged_rows=[i for i in range(1241) if i!=711],identity_coordinate_bijection=list(range(1433)),
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
    return dict(status='PASS',coordinate_map='identity',coordinates=1433,unchanged_rows=1240,
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
    squaremap={6:7,106:1267,**dict(zip(RANGE_OUTPUTS,range(1259,1267)))}
    frame=[[1,[643]],[-2,[]]]+[[-1,[v,v] if v in SQUARED_OUTPUTS else [v]] for v in ports]
    weak=[[1,[643]],[-1,[105]]]+[[-1,[v,v] if v in SQUARED_OUTPUTS else [v]] for v in ports if v!=104]
    rows=[dict(multiplier=[[1,[]]],row=2),dict(multiplier=[[1,[]]],row=47)]+[dict(multiplier=[[1,[]]],row=i) for i in range(1134,1186)]
    cuts=dict(frame=dict(polynomial=frame,row_combination=rows),
        weak=dict(polynomial=weak,row_combination=rows[:2]+[dict(multiplier=[[-1,[]]],row=88)]+rows[2:]))
    need(certificate==dict(schema='power3_and_nine_squared_frame_complete_ideals_v1',actual_power_ports=ports,
        square_map=[[v,squaremap[v]] for v in SQUARED_OUTPUTS],cuts=cuts,
        scope='Exact polynomial identities over all integers. The ordinary absolute-value frame and source semantics are separately proved.'),'complete ordinary/weak frame coefficient ledgers')
    for name,cut in cuts.items():
        result={}
        for item in cut['row_combination']:result=add(result,mul(polynomial(item['multiplier']),polynomial(raw['rows'][item['row']]['terms'])))
        need(result==polynomial(cut['polynomial']),'unbounded actual '+name+' squared-frame identity')
    return dict(status='PASS',ordinary_identity=True,weak_identity=True,actual_power_ports=43,squared_output_ports=10,zero_input_sign_premises=True)


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
    need(digest((ordinary/'MANIFEST.json').read_bytes())==pins['ordinary_manifest_sha256']=='14d504be627beaba1caf9c5f704da6762bfd693a1416a84f1bedf9d9df7197f0','exact separately sealed binomial55 source proof')
    for name in ['source/raw_builder.json','raw/parent.json','raw/domain.json','FRAME_POLICY.json','RADIUS_POLICY.json','CUTS.json','CERTIFICATE.json','PROOF.md','BOUNDARY.md']:
        need((HERE/name).read_bytes()==(ordinary/name).read_bytes(),'whole copied ordinary member '+name)
    build=load(HERE/'BUILD.json')
    need(build['generator_sha256']==digest((HERE/'build.py').read_bytes()) and build['source_pins_sha256']==digest((HERE/'SOURCE_PINS.json').read_bytes()),'producer and complete input pins')
    for name,h in build['files'].items():need(digest((HERE/name).read_bytes())==h,'whole generated equation/restoration/quartic '+name)
    original=load(baseline/'source/raw_builder.json');raw=load(HERE/'source/raw_builder.json')
    old=load(baseline/'raw/parent.json');old_domain=load(baseline/'raw/domain.json')
    parent=load(HERE/'raw/parent.json');domain=load(HERE/'raw/domain.json');cuts=load(HERE/'CUTS.json');policy=load(HERE/'FRAME_POLICY.json');radius=load(HERE/'RADIUS_POLICY.json')
    previous_policy=load(baseline/'FRAME_POLICY.json');previous_radius=load(baseline/'RADIUS_POLICY.json')
    certificate=load(HERE/'CERTIFICATE.json');guard_policy=load(HERE/'GUARD_POLICY.json')
    inputs=(original,raw,old,old_domain,parent,domain,cuts,policy,radius,previous_policy,previous_radius,certificate,guard_policy)
    binding=literal(*inputs);frame_certificate=load(HERE/'FRAME_IDENTITIES.json');frame_result=frame_identities(raw,frame_certificate)
    target=load(HERE/'cse/parent.json');bridge=load(HERE/'CSE_BRIDGE.json');bridge_result=cse_bridge(parent,target,bridge)
    mutations=[]
    def changed(position,mutation):
        values=list(inputs);values[position]=deepcopy(values[position]);mutation(values[position]);return lambda:literal(*values)
    first=certificate['new_guard_index'];rid=1186+first
    mutations.append(reject('alter unrelated body source',changed(1,lambda x:x['rows'][0]['terms'][0].__setitem__(0,-2))))
    mutations.append(reject('change actual power output to a square',changed(1,lambda x:x['powers'][3].update(output=['v',1267]))))
    mutations.append(reject('change body frame summand',changed(1,lambda x:x['rows'][1152]['terms'].__setitem__(0,[-1,[106]]))))
    mutations.append(reject('negate a new product graph',changed(4,lambda x:x['residuals'][rid]['terms'][0].__setitem__(0,-1))))
    mutations.append(reject('square only one pair member',changed(5,lambda x:x['guards'][first]['predicate'].update(terms=[[1,[123,123]]]))))
    mutations.append(reject('remove a retained anchor',changed(5,lambda x:x['guards'].__delitem__(next(i for i,g in enumerate(x['guards']) if g['predicate'].get('raw_variables')==[94])))))
    mutations.append(reject('claim source meaning from finite algebra',changed(12,lambda x:x.update(ordinary_source_equivalence_claimed=True))))
    mutations.append(reject('claim compact bridge',changed(12,lambda x:x.update(compact_bridge_assumed=True))))
    mutations.append(reject('change retained guard auxiliary metadata',changed(4,lambda x:x['variables'][-1].update(name='altered auxiliary'))))
    mutations.append(reject('lose removed-variable coverage',changed(6,lambda x:x['removed_old_auxiliary'].pop())))
    mutations.append(reject('assume whole-guarded-tuple bijection',changed(12,lambda x:x.update(whole_guarded_tuple_bijection_assumed=True))))
    mutations.append(reject('weaken joint factorial predicate',changed(8,lambda x:x['joint_guard']['predicate'].update(terms=[[1,[87]],[-1,[86]]]))))
    mutations.append(reject('alter a literal shared-sum coefficient',changed(11,lambda x:x['source_identities']['derived_anchor']['row_combination'][0]['multiplier'][0].__setitem__(0,-1))))
    mutations.append(reject('use a different unbound ordinary seal',changed(12,lambda x:x.update(ordinary_manifest_sha256='0'*64))))
    mutations.append(reject('assume nonexistent direct91 guard',changed(11,lambda x:x.update(direct_guard_on_91_assumed=True))))
    bad_frame=deepcopy(frame_certificate);bad_frame['cuts']['weak']['row_combination'][2]['multiplier']=[[1,[]]]
    mutations.append(reject('wrong inherited weak-frame cancellation',lambda:frame_identities(raw,bad_frame)))
    bad_frame2=deepcopy(frame_certificate);bad_frame2['cuts']['frame']['polynomial'][1][0]=-1
    mutations.append(reject('alter inherited complete frame constant',lambda:frame_identities(raw,bad_frame2)))
    bad_bridge=deepcopy(bridge);bad_bridge['identity_coefficients']['707'][0][0]+=1
    mutations.append(reject('alter universal modulus coefficient',lambda:cse_bridge(parent,target,bad_bridge)))
    bad_target=deepcopy(target);bad_target['residuals'][711]['terms'][0][1]=[765]
    mutations.append(reject('alias wrong modulus',lambda:cse_bridge(parent,bad_target,bridge)))
    bad_bridge2=deepcopy(bridge);bad_bridge2['pivot_coefficient']=1
    mutations.append(reject('lose unit row pivot',lambda:cse_bridge(parent,target,bad_bridge2)))
    configurations=[('retained',0,None),('support2_affine1',2,1),('support2_affine2',2,2),('support4_affine2',4,2),
        ('support8_affine2',8,2),('support16_affine2',16,2),('support32_affine2',32,2),
        ('support8_affine3',8,3),('support16_affine3',16,3),('support32_affine3',32,3),
        ('support8_default',8,None),('support16_default',16,None)]
    settings={mode+'/'+name:(cap,affine) for mode in ['raw','cse'] for name,cap,affine in configurations}
    census=load(HERE/'CENSUS.json');need(set(census)==set(settings),'all24 RAW and separately bridged CSE configurations')
    old_census=load(baseline/'CENSUS.json');comparison=[]
    for name,record in sorted(census.items()):
        previous=name;a,b=old_census[previous]['metrics'],record['metrics']
        comparison.append(dict(configuration=name,frozen557_configuration=previous,old_literal_metrics=a,new_prototype_metrics=b,
            delta={k:b[k]-a[k] for k in ['variables','quadratic_rows','expanded_monomials','max_abs_expanded_coefficient']},ordinary_source_equivalence_claimed=False))
    need(load(HERE/'MEASURED_COMPARISON.json')==dict(scope='Measured shared-binomial-digit-product arithmetic prototypes; source license is separately sealed, no accepted metric promotion.',comparisons=comparison),'all measured same-setting differences without semantic license')
    need(not (HERE/'compact').exists(),'no compact equation or assumed bridge')
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole reviewed monic projection archive')
    results={}
    with tempfile.TemporaryDirectory(prefix='shared-binomial-digit-product-independent-') as tmp,zipfile.ZipFile(archive) as z:
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
        source_pins={name:digest((HERE/name).read_bytes()) for name in ['README.md','FEASIBILITY.md','PROOF.md','BOUNDARY.md','CERTIFICATE.json','GUARD_POLICY.json','SOURCE_PINS.json','BUILD.json','RADIUS_POLICY.json','FRAME_POLICY.json','FRAME_IDENTITIES.json','CUTS.json','CSE_BRIDGE.json','MEASURED_COMPARISON.json','check.py']},
        scope='Exact shared-binomial-digit-product/55-guard RAW parent with unchanged arithmetic body, full integer frame identities, invertible CSE row identity and complete signed monic projections/quartics only. No ordinary compiler/radix/source calibration or accepted metric license.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',profiles=len(results),corruptions=len(mutations),ordinary_source_equivalence_claimed=False),sort_keys=True))


if __name__=='__main__':main()
