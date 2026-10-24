#!/usr/bin/env python3
"""Optimizer-free shared-remainder product56 RAW/CSE equations and complete quartics."""
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


GROUPS=[(574,[(576,577),(585,586),(593,594),(601,602)],[(547,548,549),(553,554,555),(559,560,561),(565,566,567)]),
 (608,[(610,611),(619,620)],[(572,573,574),(578,579,580)]),
 (626,[(628,629),(637,638)],[(585,586,587),(591,592,593)]),
 (547,[(549,550),(562,563)],[(526,527,528),(537,538,539)])]
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
    need(raw==oldraw and frame==oldframe,'ENTIRE raw body/frame/metadata identical, no port or row change')
    need((len(raw['variables']),len(raw['rows']),len(oldparent['variables']),len(oldparent['residuals']))==(1268,1186,1454,1248),'complete old/source boundary')
    need(oldparent['variables'][:1268]==raw['variables'] and oldparent['residuals'][:1186]==[dict(label=r['label'],terms=r['terms']) for r in raw['rows']],'every old body row and variable bound to source')
    single={g['predicate']['raw_variables'][0]:i for i,g in enumerate(olddomain['guards']) if g['predicate']['kind']=='retained_scalar'}
    expected_groups=[];exchanges=[];first={};second={};source_polys=[P(r['terms']) for r in raw['rows']];identities=[]
    def collect(cut,label):
        got={}
        for item in cut['row_combination']:
            need(0<=item['row']<1186,'literal body row index')
            got=add(got,mul(P(item['multiplier']),source_polys[item['row']]))
        need(got==P(cut['polynomial']),'every coefficient of actual source ideal '+label);identities.append(label)
    for N,pairs,rowids in GROUPS:
        anchor=list(pairs[0]);group=dict(denominator=N,anchor=anchor,pairs=[list(p) for p in pairs],rows=[list(r) for r in rowids],anchor_guard_indices=[single[v] for v in anchor],source_sum_cuts=[])
        for pair,ids in zip(pairs,rowids):
            cut=dict(pair=list(pair),polynomial=[[1,[N]],[-1,[pair[0]]],[-1,[pair[1]]],[-1,[]]],row_combination=[dict(row=i,multiplier=[[1,[]]]) for i in ids])
            collect(cut,'sum.'+str(pair));group['source_sum_cuts'].append(cut)
            if pair==pairs[0]:continue
            item=dict(pair=list(pair),denominator=N,anchor=anchor,old_guard_indices=[single[v] for v in pair],source_sum_rows=list(ids),anchor_sum_rows=list(rowids[0]),sum_difference_cut=dict(polynomial=[[1,[pair[0]]],[1,[pair[1]]],[-1,[anchor[0]]],[-1,[anchor[1]]]],row_combination=[dict(row=i,multiplier=[[1,[]]]) for i in rowids[0]]+[dict(row=i,multiplier=[[-1,[]]]) for i in ids]))
            collect(item['sum_difference_cut'],'anchor_difference.'+str(pair));exchanges.append(item);first[item['old_guard_indices'][0]]=item;second[item['old_guard_indices'][1]]=item
        expected_groups.append(group)
    names=deepcopy(raw['variables']);residuals=deepcopy(oldparent['residuals'][:1186]);guards=[];variable_map={i:i for i in range(1268)};retained_rows=[[i,i] for i in range(1186)];retained_indices=[];guard_map=[]
    for i,g in enumerate(olddomain['guards']):
        if i in second:
            guard_map.append(dict(old_index=i,new_index=second[i]['new_guard_index'],kind='replaced_pair_member'));continue
        j=len(guards);aux=[1268+3*j,1269+3*j,1270+3*j]
        if i in first:
            item=first[i];r,s=item['pair'];label='shared_remainder_product.'+str(r)+'.'+str(s);names.extend(dict(kind='nonnegative_guard',name=label+'.'+a) for a in ['a','b','c'])
            predicate=dict(kind='shared_remainder_product',raw_variables=[r,s],terms=[[1,[r,s]]]);a,b,c=aux
            row=dict(label=label,terms=[[1,[r,s]],[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]])
            item.update(new_guard_index=j,new_auxiliary=aux,new_parent_row=1186+j,old_auxiliary_groups=[olddomain['guards'][k]['auxiliary'] for k in item['old_guard_indices']],old_parent_rows=[1186+k for k in item['old_guard_indices']]);guard_map.append(dict(old_index=i,new_index=j,kind='replaced_pair_member'))
        else:
            predicate=deepcopy(g['predicate']);remap=dict(zip(g['auxiliary'],aux))
            for a,b in zip(g['auxiliary'],aux):variable_map[a]=b;names.append(deepcopy(oldparent['variables'][a]))
            row=dict(label=oldparent['residuals'][1186+i]['label'],terms=[[c,[remap.get(v,v) for v in m]] for c,m in oldparent['residuals'][1186+i]['terms']]);retained_rows.append([1186+i,1186+j]);retained_indices.append(i);guard_map.append(dict(old_index=i,new_index=j,kind='retained'))
        guards.append(dict(auxiliary=aux,predicate=predicate));residuals.append(row)
    expected_parent=deepcopy(oldparent);expected_parent.update(variant='shared_remainder_product_guards56_raw_literal',variables=names,residuals=residuals)
    need(parent==expected_parent,'EVERY new parent row/variable/label/attribute exact; all other guards retained')
    need((len(names),len(residuals),len(guards))==(1436,1242,56),'actual complete new parent census')
    need(sum(g['predicate']['kind']=='retained_scalar' for g in guards)==47 and sum(g['predicate']['kind']=='shared_remainder_product' for g in guards)==6,'47 old scalars,6 products,3 preserved replacements')
    anchor_indices={i for g in expected_groups for i in g['anchor_guard_indices']}
    need(anchor_indices<=set(retained_indices) and len(anchor_indices)==8,'all eight direct anchor scalar graphs explicitly retained')
    for j,(guard,row) in enumerate(zip(guards,residuals[1186:])):
        a,b,c=guard['auxiliary'];target=add(P(guard['predicate']['terms']),P([[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]))
        need(P(row['terms'])==target and guard['auxiliary']==list(range(1268+3*j,1271+3*j)),'every complete actual Legendre graph and contiguous triple')
    wantdomain=dict(baseline_body_variables=1268,baseline_body_rows=1186,baseline_raw_indices=list(range(1268)),guards=guards,predicates=56,original_scalar_predicates=47,shared_remainder_product_predicates=6,replaced_scalar_pairs=[x['pair'] for x in exchanges],retained_anchor_pairs=[g['anchor'] for g in expected_groups],inherited_removed_power_output_variables=[6,106],inherited_absent_quotient_variables=olddomain['inherited_absent_quotient_variables'],raw_source='source/raw_builder.json',frame_policy='FRAME_POLICY.json',radius_policy='RADIUS_POLICY.json',guard_policy='CERTIFICATE.json',compact_bridge_assumed=False,ordinary_source_equivalence_proved_separately=True)
    need(domain==wantdomain,'entire56 predicate domain, pair/anchor/scope metadata')
    wanted_radius=deepcopy(oldradius);wanted_radius['joint_guard']=dict(index=55,predicate=guards[55]['predicate'],auxiliary=guards[55]['auxiliary'])
    need(radius==wanted_radius and guards[55]['auxiliary']==[1433,1434,1435],'all radius laws exact, only joint graph index/auxiliary binding changes')
    wantcuts=dict(source_row_map=[[i,i] for i in range(1186)],source_variables_unchanged=True,source_rows_unchanged=True,retained_parent_rows=retained_rows,guard_index_map=guard_map,retained_old_guard_indices=retained_indices,replaced_guard_indices=sorted(set(first)|set(second)),retained_old_variable_map=[[i,variable_map[i]] for i in sorted(variable_map)],removed_old_auxiliary=sorted(set(range(1454))-set(variable_map)),new_product_auxiliary=sorted(a for x in exchanges for a in x['new_auxiliary']),auxiliary_zero_sets_identified_pointwise=False,raw_coordinate_projection='identity',quantification='For each unrestricted integer tuple satisfying the unchanged1186 body residuals, existence of old62guard witnesses iff existence of new56guard witnesses.')
    need(cuts==wantcuts and len(cuts['removed_old_auxiliary'])==36 and len(cuts['new_product_auxiliary'])==18,'complete row/coordinate/guard replacement maps, no whole-auxiliary bijection')
    expected_certificate=dict(schema='shared_remainder_product_guard_equivalence_v1',body_variables=1268,body_rows=1186,old_parent_variables=1454,old_parent_rows=1248,old_predicates=62,new_parent_variables=1436,new_parent_rows=1242,new_predicates=56,retained_scalars=47,new_product_predicates=6,groups=expected_groups,exchanges=exchanges,legendre_graph=dict(polynomial='u-a^2-b^2-c^2-c',auxiliary_domain='all integers',represented_values='all nonnegative integers'),raw_body_byte_unchanged=True,all_power_and_frame_ports_unchanged=True,full_old_numerical_endpoint_inherited=True,direct_anchor_signs_used_before_product_restoration=True,nonnegative_denominators_not_assumed=True,positive_pair_or_pell_semantics_used=False,ordinary_equivalence_proof='PROOF.md',projected_metrics_claimed=False,new_lean_claim=False)
    need(certificate==expected_certificate,'every group,cut coefficient,pair/anchor/old-new graph and scope record exact')
    return dict(status='PASS',body_coordinates=1268,body_rows=1186,old_parent_coordinates=1454,new_parent_coordinates=1436,old_parent_rows=1248,new_parent_rows=1242,predicates=56,retained_scalars=47,product_predicates=6,preserved_replacement_predicates=3,collected_source_identities=len(identities),identity_labels=identities,complete_legendre_graphs=56,retained_anchor_scalar_graphs=8,removed_old_auxiliary=36,new_product_auxiliary=18,whole_raw_projection='identity',whole_guarded_tuple_bijection_claimed=False,power_or_frame_meaning_used=False)

RANGE_OUTPUTS=[573,583,591,599,607,617,625,635]
SQUARED_OUTPUTS=[6,106]+RANGE_OUTPUTS
polynomial=P


def literal(original,raw,old,old_domain,parent,domain,cuts,frame,radius,previous_frame,previous_radius,certificate,guard_policy):
    result=guard_binding([raw,parent,domain,frame,radius,certificate,cuts],[original,old,old_domain,previous_frame,previous_radius])
    copied=['source/raw_builder.json','raw/parent.json','raw/domain.json','FRAME_POLICY.json','RADIUS_POLICY.json','CUTS.json','CERTIFICATE.json','PROOF.md','BOUNDARY.md']
    want=dict(schema='shared_remainder_product_guards56_finite_binding_v1',ordinary_packet='research/shared-remainder-product-guards',ordinary_manifest_sha256='8678f1226872f49759c6527cea7e8e0a334603a9b9a2b9d58776e432c11c8a6c',copied_ordinary_files=copied,arithmetic_body_unchanged_from_baseline=True,raw_parent_and_domain_byte_identical_to_ordinary=True,new_body_gates=0,replaced_scalar_pairs=[x['pair'] for x in certificate['exchanges']],retained_anchor_pairs=[g['anchor'] for g in certificate['groups']],body_coordinates=1268,body_rows=1186,predicates=56,retained_scalar_predicates=47,new_product_predicates=6,preserved_replacement_predicates=3,raw_body_projection='identity',guard_auxiliaries_reconstructed_existentially=True,whole_guarded_tuple_bijection_assumed=False,ordinary_source_equivalence_claimed=False,compact_bridge_assumed=False,accepted_metrics_promoted=False,scope='Finite complete RAW/CSE algebra/projection/quartic candidate. Ordinary same-body guard-domain equivalence comes only from the separately sealed ordinary packet. No projected count is inferred from guard removal.')
    need(guard_policy==want,'complete accepted ordinary license and finite-only guard policy')
    return result


def cse_bridge(parent,target,certificate):
    need(len(parent['variables'])==1436 and len(parent['residuals'])==1242,'complete RAW source for row identity')
    want=deepcopy(parent);want['variant']='shared_remainder_product_guards56_modulus_alias'
    want['residuals'][711]=dict(label='common_radius.base_modulus_alias',terms=[[1,[764]],[-1,[730]]])
    need(target==want,'whole CSE parent changes exactly row711 and variant; all coordinates and other rows identical')
    q=[[1,[112]],[1,[92]],[-1,[695]]];minusq=[[-c,m] for c,m in q]
    coeffs={str(i):[[c,[]]] for i,c in [(711,-1),(707,1),(708,-1),(709,-1),(710,-1),(673,-1),(674,1),(675,1),(676,1),(677,1)]}
    coeffs.update({'90':minusq,'92':minusq,'77':q})
    need(certificate==dict(schema='common_radius_unit_row_operation_v1',source='raw/parent.json',target='cse/parent.json',
        replaced_row=711,pivot_coefficient=-1,old_row=parent['residuals'][711],new_row=target['residuals'][711],
        identity_coefficients=coeffs,unchanged_rows=[i for i in range(1242) if i!=711],identity_coordinate_bijection=list(range(1436)),
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
    return dict(status='PASS',coordinate_map='identity',coordinates=1436,unchanged_rows=1241,
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
    need(digest((ordinary/'MANIFEST.json').read_bytes())==pins['ordinary_manifest_sha256']=='8678f1226872f49759c6527cea7e8e0a334603a9b9a2b9d58776e432c11c8a6c','exact separately sealed shared56 source proof')
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
    first=certificate['exchanges'][0]['new_guard_index'];rid=1186+first
    mutations.append(reject('alter unrelated body source',changed(1,lambda x:x['rows'][0]['terms'][0].__setitem__(0,-2))))
    mutations.append(reject('change actual power output to a square',changed(1,lambda x:x['powers'][3].update(output=['v',1267]))))
    mutations.append(reject('change body frame summand',changed(1,lambda x:x['rows'][1152]['terms'].__setitem__(0,[-1,[106]]))))
    mutations.append(reject('negate a new product graph',changed(4,lambda x:x['residuals'][rid]['terms'][0].__setitem__(0,-1))))
    mutations.append(reject('square only one pair member',changed(5,lambda x:x['guards'][first]['predicate'].update(terms=[[1,[585,585]]]))))
    mutations.append(reject('remove a retained anchor',changed(5,lambda x:x['guards'].__delitem__(next(i for i,g in enumerate(x['guards']) if g['predicate'].get('raw_variables')==[576])))))
    mutations.append(reject('claim source meaning from finite algebra',changed(12,lambda x:x.update(ordinary_source_equivalence_claimed=True))))
    mutations.append(reject('claim compact bridge',changed(12,lambda x:x.update(compact_bridge_assumed=True))))
    mutations.append(reject('change retained guard auxiliary metadata',changed(4,lambda x:x['variables'][-1].update(name='altered auxiliary'))))
    mutations.append(reject('lose removed-variable coverage',changed(6,lambda x:x['removed_old_auxiliary'].pop())))
    mutations.append(reject('assume whole-guarded-tuple bijection',changed(12,lambda x:x.update(whole_guarded_tuple_bijection_assumed=True))))
    mutations.append(reject('weaken joint factorial predicate',changed(8,lambda x:x['joint_guard']['predicate'].update(terms=[[1,[87]],[-1,[86]]]))))
    mutations.append(reject('alter a literal shared-sum coefficient',changed(11,lambda x:x['groups'][0]['source_sum_cuts'][0]['row_combination'][0]['multiplier'][0].__setitem__(0,-1))))
    mutations.append(reject('use a different unbound ordinary seal',changed(12,lambda x:x.update(ordinary_manifest_sha256='0'*64))))
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
        comparison.append(dict(configuration=name,frozen569_configuration=previous,old_literal_metrics=a,new_prototype_metrics=b,
            delta={k:b[k]-a[k] for k in ['variables','quadratic_rows','expanded_monomials','max_abs_expanded_coefficient']},ordinary_source_equivalence_claimed=False))
    need(load(HERE/'MEASURED_COMPARISON.json')==dict(scope='Measured shared-remainder-product arithmetic prototypes; source license is separately sealed, no accepted metric promotion.',comparisons=comparison),'all measured same-setting differences without semantic license')
    need(not (HERE/'compact').exists(),'no compact equation or assumed bridge')
    archive=REPO/pins['archive'];need(digest(archive.read_bytes())==pins['archive_sha256'],'whole reviewed monic projection archive')
    results={}
    with tempfile.TemporaryDirectory(prefix='shared-remainder-product-independent-') as tmp,zipfile.ZipFile(archive) as z:
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
        scope='Exact shared-remainder-product/56-guard RAW parent with unchanged arithmetic body, full integer frame identities, invertible CSE row identity and complete signed monic projections/quartics only. No ordinary compiler/radix/source calibration or accepted metric license.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',profiles=len(results),corruptions=len(mutations),ordinary_source_equivalence_claimed=False),sort_keys=True))


if __name__=='__main__':main()
