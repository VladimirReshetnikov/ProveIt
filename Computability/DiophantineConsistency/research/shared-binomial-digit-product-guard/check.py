#!/usr/bin/env python3
"""Independent stdlib audit of a derived-anchor binomial digit product guard."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def need(ok,why):
    if not ok:raise ValueError(why)
def load(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
def P(terms):
    out={}
    for c,m in terms:
        need(type(c) is int and all(type(v) is int for v in m),'literal integer polynomial')
        k=tuple(sorted(m));out[k]=out.get(k,0)+c
    return {m:c for m,c in out.items() if c}
def add(a,b):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}
def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return {m:c for m,c in out.items() if c}
def sealed(folder):
    f=folder/'MANIFEST.json';records=load(f)['files'];need(set(records)=={str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p!=f},'closed complete inventory '+str(folder))
    for n,h in records.items():need(digest(folder/n)==h,'complete sealed member '+n)
def verify(values,old):
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
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True,type=Path);args=p.parse_args();pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest(ROOT/n)==h,'whole frozen input '+n)
    base=ROOT/pins['accepted_profile_packet'];ordinary=ROOT/pins['accepted_ordinary_packet'];sealed(base);sealed(ordinary)
    need(digest(base/'MANIFEST.json')==pins['accepted_profile_manifest_sha256']=='19fc65a27b18920d916922025fc07e80741ef255d59cf8a15edb6d33c29ba551','exact557 finite whole seal')
    need(digest(ordinary/'MANIFEST.json')==pins['accepted_ordinary_manifest_sha256']=='8678f1226872f49759c6527cea7e8e0a334603a9b9a2b9d58776e432c11c8a6c','complete56 ordinary numerical theorem')
    if (HERE/'MANIFEST.json').exists():sealed(HERE)
    b=load(HERE/'BUILD.json');need(b['generator_sha256']==digest(HERE/'build.py') and b['source_pins_sha256']==digest(HERE/'SOURCE_PINS.json'),'whole literal builder and pins bound')
    need(set(b['files'])=={'source/raw_builder.json','raw/parent.json','raw/domain.json','FRAME_POLICY.json','RADIUS_POLICY.json','CUTS.json','CERTIFICATE.json'},'complete seven generated members')
    for n,h in b['files'].items():need(digest(HERE/n)==h,'whole materialized artifact '+n)
    need((HERE/'source/raw_builder.json').read_bytes()==(base/'source/raw_builder.json').read_bytes() and (HERE/'FRAME_POLICY.json').read_bytes()==(base/'FRAME_POLICY.json').read_bytes(),'literal raw body/frame bytes unchanged')
    old=[load(base/n) for n in ['source/raw_builder.json','raw/parent.json','raw/domain.json','FRAME_POLICY.json','RADIUS_POLICY.json']];values=[load(HERE/n) for n in ['source/raw_builder.json','raw/parent.json','raw/domain.json','FRAME_POLICY.json','RADIUS_POLICY.json','CERTIFICATE.json','CUTS.json']];binding=verify(values,old);rejected=[]
    def reject(label,position,mutate):
        v=deepcopy(values);mutate(v[position])
        try:verify(v,old)
        except (ValueError,KeyError,TypeError,IndexError):rejected.append(label)
        else:raise ValueError('accepted actual corruption '+label)
    reject('change derived-anchor body row',0,lambda x:x['rows'][85]['terms'][0].__setitem__(0,-1))
    reject('change target digit bound body row',0,lambda x:x['rows'][542]['terms'][0].__setitem__(0,-1))
    reject('change actual power output',0,lambda x:x['powers'][3].update(output=['v',1267]))
    reject('change a squared frame port',0,lambda x:x['rows'][1152]['terms'].__setitem__(0,[-1,[106]]))
    reject('change raw operand variable metadata',1,lambda x:x['variables'][123].update(name='wrong'))
    reject('negate product graph',1,lambda x:x['residuals'][1203]['terms'][0].__setitem__(0,-1))
    reject('omit product auxiliary square',1,lambda x:x['residuals'][1203]['terms'].__delitem__(2))
    reject('reuse old auxiliary metadata',1,lambda x:x['variables'][1319].update(name='choose2.output.oldguard'))
    reject('square only one product operand',2,lambda x:x['guards'][17]['predicate'].update(terms=[[1,[123,123]]]))
    for i in [12,13,23]:reject('remove retained anchor-source graph '+str(i),2,lambda x,i=i:x['guards'].__delitem__(i))
    inherited=next(i for i,g in enumerate(values[2]['guards']) if g['predicate']['kind']=='shared_remainder_product')
    reject('omit inherited remainder product',2,lambda x:x['guards'].__delitem__(inherited))
    reject('omit paired-index predicate',2,lambda x:x['guards'].__delitem__(53))
    reject('claim a new frame policy',3,lambda x:x.update(actual_power_requests_unchanged=False))
    reject('weaken retained joint factorial guard',4,lambda x:x['joint_guard']['predicate'].update(terms=[[1,[87]],[-1,[86]]]))
    reject('assume91 directly guarded',5,lambda x:x.update(direct_guard_on_91_assumed=True))
    reject('change positive anchor constant',5,lambda x:x['source_identities']['derived_anchor']['polynomial'][-1].__setitem__(0,1))
    reject('omit anchor-source row85',5,lambda x:x['source_identities']['derived_anchor']['row_combination'].pop())
    reject('flip anchored difference coefficient',5,lambda x:x['source_identities']['anchored_difference']['row_combination'][0]['multiplier'][0].__setitem__(0,-1))
    reject('bind wrong raw pair',5,lambda x:x.update(pair=[123,551]))
    reject('omit a direct anchor premise',5,lambda x:x['direct_anchor_source'].pop())
    reject('use Pell meaning before restoration',5,lambda x:x.update(denominator_or_pell_meaning_used=True))
    reject('claim projected metrics',5,lambda x:x.update(projected_metrics_claimed=True))
    reject('lose a former guard in full map',6,lambda x:x['guard_index_map'].pop())
    reject('lose removed auxiliary coverage',6,lambda x:x['removed_old_auxiliary'].pop())
    reject('identify entire guarded tuples',6,lambda x:x.update(auxiliary_zero_sets_identified_pointwise=True))
    need((-1)*(-1)>=0 and -1+-1<0,'product alone fails')
    need(-1+2>=1 and (-1)*2<0,'positive sum alone fails')
    need(0+1>=1 and 0*1==0,'zero product endpoint retained')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),literal_and_source_ideal_audit=binding,rejected_corruptions=rejected,boundary_controls_checked=3,finite_controls_replace_unbounded_proof=False,ordinary_equivalence_proof='PROOF.md',complete_ordinary_equivalence=True,projected_metrics_claimed=False,optimizer_or_parent_checker_or_incoming_program_or_lean_executed=False,canonical_or_common_files_modified=False,source_pins={n:digest(HERE/n) for n in ['PROOF.md','BOUNDARY.md','README.md','SOURCE_PINS.json','BUILD.json','CERTIFICATE.json','CUTS.json','build.py','check.py']},scope='Uniform all-integer fixed-body tuple guard equivalence, four literal source ideals, all55 guard graphs and complete maps. PROOF.md supplies the unbounded argument. No projected census or Lean theorem.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse different existing output')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS',source_identities=4,predicates=55,rejected=len(rejected),body_unchanged=True),sort_keys=True))
if __name__=='__main__':main()
