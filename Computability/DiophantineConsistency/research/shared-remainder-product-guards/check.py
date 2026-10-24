#!/usr/bin/env python3
"""Independent stdlib literal/source-ideal audit for six anchored product guards."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
GROUPS=[(574,[(576,577),(585,586),(593,594),(601,602)],[(547,548,549),(553,554,555),(559,560,561),(565,566,567)]),
 (608,[(610,611),(619,620)],[(572,573,574),(578,579,580)]),
 (626,[(628,629),(637,638)],[(585,586,587),(591,592,593)]),
 (547,[(549,550),(562,563)],[(526,527,528),(537,538,539)])]
def need(ok,why):
    if not ok:raise ValueError(why)
def load(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
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
def sealed(folder):
    f=folder/'MANIFEST.json';records=load(f)['files'];actual={str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p!=f}
    need(set(records)==actual,'closed whole inventory '+str(folder))
    for n,h in records.items():need(digest(folder/n)==h,'whole sealed member '+n)

def verify(values,old):
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

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True,type=Path);args=p.parse_args();pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest(ROOT/n)==h,'entire frozen input '+n)
    base=ROOT/pins['accepted_profile_packet'];ordinary=ROOT/pins['accepted_ordinary_packet'];sealed(base);sealed(ordinary)
    need(digest(base/'MANIFEST.json')==pins['accepted_profile_manifest_sha256']=='f2ec7687ac03a9270c39ad839a0b1170499d186743037f9a2a30ff196795fed3','exact frozen62 profile seal')
    need(digest(ordinary/'MANIFEST.json')==pins['accepted_ordinary_manifest_sha256']=='f194d708238d78f7f4a182d0e6052aeb277e2da2ceb0d131b930f428c786b269','exact complete ordinary62 theorem')
    if (HERE/'MANIFEST.json').exists():sealed(HERE)
    build=load(HERE/'BUILD.json');need(build['generator_sha256']==digest(HERE/'build.py') and build['source_pins_sha256']==digest(HERE/'SOURCE_PINS.json'),'whole literal builder and input binding')
    need(set(build['files'])=={'source/raw_builder.json','raw/parent.json','raw/domain.json','FRAME_POLICY.json','RADIUS_POLICY.json','CUTS.json','CERTIFICATE.json'},'exact generated literal members')
    for n,h in build['files'].items():need(digest(HERE/n)==h,'whole generated materialization '+n)
    need((HERE/'source/raw_builder.json').read_bytes()==(base/'source/raw_builder.json').read_bytes() and (HERE/'FRAME_POLICY.json').read_bytes()==(base/'FRAME_POLICY.json').read_bytes(),'whole raw source and frame policy bytes identical')
    old=[load(base/n) for n in ['source/raw_builder.json','raw/parent.json','raw/domain.json','FRAME_POLICY.json','RADIUS_POLICY.json']]
    values=[load(HERE/n) for n in ['source/raw_builder.json','raw/parent.json','raw/domain.json','FRAME_POLICY.json','RADIUS_POLICY.json','CERTIFICATE.json','CUTS.json']];binding=verify(values,old);rejected=[]
    def reject(name,position,mutation):
        v=deepcopy(values);mutation(v[position])
        try:verify(v,old)
        except (ValueError,KeyError,TypeError,IndexError):rejected.append(name)
        else:raise ValueError('corruption accepted '+name)
    first=values[5]['exchanges'][0]['new_guard_index'];row=1186+first
    reject('change a native source row',0,lambda x:x['rows'][0]['terms'][0].__setitem__(0,-2))
    reject('reuse old linear106 frame',0,lambda x:x['rows'][1152]['terms'].__setitem__(0,[-1,[106]]))
    reject('truncate actual power requests',0,lambda x:x['powers'].pop())
    reject('alter preserved body variable metadata',1,lambda x:x['variables'][106].update(name='altered'))
    reject('negate product guard',1,lambda x:x['residuals'][row]['terms'][0].__setitem__(0,-1))
    reject('drop product graph square',1,lambda x:x['residuals'][row]['terms'].__delitem__(3))
    reject('reuse auxiliary name',1,lambda x:x['variables'][-1].update(name='old witness'))
    reject('restore scalar instead of product',2,lambda x:x['guards'][first]['predicate'].update(kind='retained_scalar',terms=[[1,[585]]]))
    reject('square only first pair coordinate',2,lambda x:x['guards'][first]['predicate'].update(terms=[[1,[585,585]]]))
    anchor=next(i for i,g in enumerate(values[2]['guards']) if g['predicate'].get('raw_variables')==[576])
    reject('remove direct anchor graph',2,lambda x:x['guards'].__delitem__(anchor))
    reject('drop paired-slack predicate',2,lambda x:x['guards'].__delitem__(54))
    reject('weaken joint factorial guard',4,lambda x:x['joint_guard']['predicate'].update(terms=[[1,[87]],[-1,[86]]]))
    reject('claim changed frame source',3,lambda x:x.update(actual_power_requests_unchanged=False))
    reject('wrong shared denominator',5,lambda x:x['exchanges'][3].update(denominator=574))
    reject('alter source sum constant',5,lambda x:x['groups'][0]['source_sum_cuts'][0]['polynomial'][-1].__setitem__(0,1))
    reject('omit one of ten source sums',5,lambda x:x['groups'][0]['source_sum_cuts'].pop())
    reject('flip anchor difference coefficient',5,lambda x:x['exchanges'][0]['sum_difference_cut']['row_combination'][0]['multiplier'][0].__setitem__(0,-1))
    reject('replace retained anchor by different pair',5,lambda x:x['groups'][0].update(anchor=[585,586]))
    reject('make positive Pell interpretation a premise',5,lambda x:x.update(positive_pair_or_pell_semantics_used=True))
    reject('claim projected metrics',5,lambda x:x.update(projected_metrics_claimed=True))
    reject('omit old guard coverage',6,lambda x:x['guard_index_map'].pop())
    reject('omit removed old auxiliaries',6,lambda x:x['removed_old_auxiliary'].pop())
    reject('identify guarded tuples pointwise',6,lambda x:x.update(auxiliary_zero_sets_identified_pointwise=True))
    # Counterexamples show why the precise mathematical premises matter; they are not a proof by sampling.
    need((-1)*(-1)>=0 and -1+-1<0,'product alone does not give two signs')
    need(-1+1==0 and (-1)*1<0,'anchored sum alone does not give two signs')
    need(0+0==0 and 0*0==0,'zero-sum endpoint retained')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),literal_and_source_ideal_audit=binding,rejected_corruptions=rejected,boundary_counterexamples_checked=3,finite_controls_replace_unbounded_proof=False,ordinary_equivalence_proof='PROOF.md',complete_ordinary_equivalence=True,projected_metrics_claimed=False,optimizer_or_parent_checker_or_incoming_program_or_lean_executed=False,canonical_or_common_files_modified=False,source_pins={n:digest(HERE/n) for n in ['PROOF.md','BOUNDARY.md','README.md','SOURCE_PINS.json','BUILD.json','CERTIFICATE.json','CUTS.json','build.py','check.py']},scope='Whole unchanged integer body and56guard materialization; all ten source sums/six anchored differences. Unbounded Legendre/pair/projection proof is PROOF.md. No projected census or new Lean theorem.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse different existing output')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS',source_identities=16,predicates=56,rejected=len(rejected),body_unchanged=True),sort_keys=True))
if __name__=='__main__':main()
