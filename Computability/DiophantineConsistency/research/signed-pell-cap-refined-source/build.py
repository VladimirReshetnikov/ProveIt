#!/usr/bin/env python3
"""Combined refined SOURCE ONLY; no execution before both full reviews/release."""
import argparse,copy,hashlib,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'research/signed-pell-cap-source'
LEGACY=ROOT/'con-zfc-diophantine-forms/125-unified-binomial-round15/direct/unified_reparam_derived_shell'
SEALS={'research/signed-pell-cap-source':'53244a0a26bcfe2411c28adf2c6d74f7a4618c0c42c7904e8818be4e3f9a6ef5','research/signed-pell-cap-unoriented':'9fbb6fc816b0526bc16285c5198a2c7ffa179bdf4e1f9331fc83605d639e8be2','research/signed-pell-cap-factorial-output-guard':'e5c75ddaf0a8aebc23ced3b780122a15bbfdf317ea59e2457af32e755e0e0886','research/signed-pell-cap-helper-reflection':'77d184efa8282e84c68b3252bfd41bb9cecb31c4983fb2d0824dfd8c8d77a493'}
CHRONOLOGY=['normalize_helper','absolute_frame_and_nonzero_t','unoriented_cap_with_signed_targets','signed_A_q_support_at_t','same_t_base_one_safe_F_output','F_ge_one_and_restore_F_graph','unoriented_existence_to_fresh_positive_old_source']
def need(b,s):
    if not b:raise ValueError(s)
def get(p):return json.loads(p.read_bytes())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def encode(x):return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
def P(ts):
    out={}
    for c,m in ts:k=tuple(sorted(m));out[k]=out.get(k,0)+c
    return {m:c for m,c in out.items() if c}
def T(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def V(i):return {(i,):1}
def C(c):return {():c} if c else {}
def add(*ps):
    out={}
    for p in ps:
        for m,c in p.items():out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}
def scale(p,c):return {m:c*v for m,v in p.items() if c*v}
def mul(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return {m:c for m,c in out.items() if c}
def moved(ts,mp):return T({tuple(sorted(mp[i] for i in m)):c for m,c in P(ts).items()})
def graph(expr,aux):
    a,b,c=aux;return add(expr,{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})
def authenticate():
    pins=get(HERE/'SOURCE_PINS.json')
    for section,base in [('files',ROOT),('core',HERE)]:
        for n,h in pins[section].items():need(digest(base/n)==h,'whole '+section+' '+n)
    for n,h in pins['closed_dependencies'].items():
        d=ROOT/n;need(digest(d/'MANIFEST.json')==h,'closed dependency seal '+n);need(get(d/'MANIFEST.json')['files']=={str(p.relative_to(d)):digest(p) for p in d.rglob('*') if p.is_file() and p!=d/'MANIFEST.json'},'whole closed dependency '+n)
    need(all(pins['closed_dependencies'].get(n)==h for n,h in SEALS.items()),'all four exact accepted ordinary/literal seals')
def produce():
    authenticate();body=get(PARENT/'source.json');old=get(PARENT/'guarded.json');domain=get(PARENT/'domain.json')['guards'];parentmap=dict(get(PARENT/'TRANSFORM.json')['raw_to_body']);budget=get(LEGACY/'transform_certificate.json')['square_budget']
    need(body['residuals'][217]['label']=='index_cap.lower_guard' and body['residuals'][219]['label']=='index_cap.joint_residue','exact cap row interface')
    dropbody={396,397,398};bodykeep=[i for i in range(len(body['variables'])) if i not in dropbody];bm={i:j for j,i in enumerate(bodykeep)};rows=[];bodyrows={}
    capterm=mul(add(V(387),scale(V(245),-1)),add(V(387),scale(V(245),-1)))
    for i,r in enumerate(body['residuals']):
        if i==217:continue
        q=copy.deepcopy(r)
        if i==219:q['terms']=T(add(P(q['terms']),scale(capterm,-1)))
        q['terms']=moved(q['terms'],bm);bodyrows[i]=len(rows);rows.append(q)
    source=dict(schema='refined_signed_pell_cap_body_v1',domain='unrestricted integers',variant='unoriented_signed_cap_F_unrestricted_helper_base_guard_source_only',variables=[body['variables'][i] for i in bodykeep],residuals=rows,polynomial='sum of squares of all residuals',parent_source_manifest_sha256=SEALS['research/signed-pell-cap-source'],ordinary_manifests_sha256={n:h for n,h in SEALS.items() if n!='research/signed-pell-cap-source'})
    guarded=copy.deepcopy(source);guards=[];vm=dict(bm);rm=dict(bodyrows);omitted={2,27,30};removed=set(dropbody);removedrows={217};omitted_specs=[]
    for g in domain:
        j=g.get('original_guard_index')
        if g['kind']=='cap_lower' or j in omitted:
            omitted_specs.append(copy.deepcopy(g));removed|=set(g['auxiliary']);removedrows.add(g['row']);continue
        q=copy.deepcopy(g);q['expression']=moved(q['expression'],bm)
        if 'coordinate' in q:q['coordinate']=bm[q['coordinate']]
        if 'pair' in q:q['pair']=[bm[i] for i in q['pair']]
        if j is not None:
            aux=list(range(len(guarded['variables']),len(guarded['variables'])+3));vm.update(zip(g['auxiliary'],aux));q.update(auxiliary=aux,row=len(guarded['residuals']));rm[g['row']]=q['row']
            guarded['variables'] += [old['variables'][i] for i in g['auxiliary']];guarded['residuals'].append(dict(label='domain_guard.'+str(j),terms=T(graph(P(q['expression']),aux))))
        else:q['auxiliary']=[bm[i] for i in g['auxiliary']];q['row']=bodyrows[g['row']]
        guards.append(q)
    for g in omitted_specs:
        for v in g['auxiliary']:need([i for i,r in enumerate(old['residuals']) if any(v in m for c,m in r['terms'])]==[g['row']],'complete omitted graph privacy')
    aux=list(range(len(guarded['variables']),len(guarded['variables'])+3));expr=add(V(bm[255]),C(-4));helper_spec=dict(kind='comparison_base_lower',expression=T(expr),auxiliary=aux,row=len(guarded['residuals']),replaces_original_guard_indices=[27,30]);guards.append(helper_spec)
    guarded['variables'] += [dict(name='helper_base_lower.'+s,kind='integer_guard') for s in ['a','b','c']];guarded['residuals'].append(dict(label='domain_guard.helper_base_lower',terms=T(graph(expr,aux))))
    need(set(vm)==set(range(len(old['variables'])))-removed and set(rm)==set(range(len(old['residuals'])))-removedrows,'complete old coordinate/row namespaces')
    rawmap={i:bm[j] for i,j in parentmap.items() if j in bm};seeds=[]
    for s in get(PARENT/'TRANSFORM.json')['all_original_seeds']:
        q=copy.deepcopy(s);q['pair']=[rawmap[i] for i in q['pair']];q['target']=moved(q['target'],rawmap);seeds.append(q)
    atoms=[dict(token=a['token'],affine=moved(a['affine'],rawmap)) for a in budget['atoms']];calls=[{k:moved(p[k],rawmap) for k in ['base','exponent','output']} for p in budget['power_calls']]
    reflection={str(bm[i]):moved(T(p),bm) for i,p in [(251,scale(V(251),-1)),(252,add(C(-2),scale(V(252),-1))),(254,scale(V(254),-1)),(375,add(C(-2),scale(V(375),-1)))]}
    plan=dict(schema='refined_signed_cap_source_literal_map_v1',parent_manifest_sha256=SEALS['research/signed-pell-cap-source'],ordinary_manifests_sha256=source['ordinary_manifests_sha256'],old_body_to_new=[[i,bm[i]] for i in bodykeep],old_guarded_to_new=[[i,vm[i]] for i in sorted(vm)],old_row_to_new=[dict(old_row=i,new_row=rm.get(i),status=('removed_graph' if i in removedrows else 'primary_pool_cap_term_removed' if i==219 else 'retained')) for i in range(len(old['residuals']))],removed_private_coordinates=sorted(removed),removed_graphs=omitted_specs,new_helper_graph=helper_spec,all_original_seeds=seeds,all37_frame_atoms=atoms,all18_power_calls=calls,reflection=reflection,chronology=CHRONOLOGY,native_front_old=list(range(246))+list(range(376,386)),native_front_new=[bm[i] for i in list(range(246))+list(range(376,386))],pool_quotient_transfer='At an old cap-source zero, h_new=h_old-(C-W)^2/(A-1); integrality follows from the accepted old cap theorem. Soundness reconstructs a fresh positive private Pell tuple after signed-A t-only F recovery.',old_whole_body_identity_claimed=False,A_positive_assumed_before_F=False,all_target_positivity_used_before_F=False,source_only=True,optimizer_factorization_projection_executed=False,accepted_frontier_claim=False)
    return {'source.json':source,'guarded.json':guarded,'domain.json':dict(schema='refined_signed_cap_source_domain_v1',guards=guards),'TRANSFORM.json':plan}
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');p.add_argument('--destination',type=Path,default=HERE);p.add_argument('--output',type=Path,required=True);a=p.parse_args();artifacts=produce()
    for n,d in artifacts.items():
        data=encode(d);target=a.destination/n
        if a.check:need(target.read_bytes()==data,'whole deterministic source '+n)
        else:need(not target.exists() or target.read_bytes()==data,'refuse changed source overwrite '+n);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_only=True,pure_check=a.check,generated={n:hashlib.sha256(encode(d)).hexdigest() for n,d in artifacts.items()},source_pins_sha256=digest(HERE/'SOURCE_PINS.json'),optimizer_factorization_projection_executed=False,source_acceptance_or_frontier_claim=False);text=encode(result);need(not a.output.exists() or a.output.read_bytes()==text,'refuse changed receipt');a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(text);print(text.decode(),end='')
if __name__=='__main__':main()
