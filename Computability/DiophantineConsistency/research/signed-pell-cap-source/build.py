#!/usr/bin/env python3
"""Source-only joint signed-cap candidate; execution requires prior code review."""
import argparse,json,sys
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
ORDINARY=ROOT/'research/signed-pell-cap'
PARENT=ROOT/'con-zfc-diophantine-forms/125-unified-binomial-round15/direct/unified_reparam_derived_shell'
ORDINARY_SEAL='f5aefb843a055aa2de7151bd6fceab54288b7566b7bbd386dc5f4928fe7aa8c8'
PARENT_SHA='0b36a5ff088aece09f23dff8f55a2c6904e1f69615f16c4a5299acb1fa790c67'
RAW=ROOT/'con-zfc-diophantine-forms/125-unified-binomial-round15/architecture/unified_derived_shell/raw/raw_audit_input.json'
def need(ok,why):
    if not ok:raise ValueError(why)
def load(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
def encode(d):return (json.dumps(d,indent=2,sort_keys=True)+'\n').encode()
def poly(terms):
    out={}
    for c,m in terms:
        key=tuple(sorted(m));out[key]=out.get(key,0)+c
    return {m:c for m,c in out.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def add(*items):
    out={}
    for p in items:
        for m,c in p.items():out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}
def neg(p):return {m:-c for m,c in p.items()}
def V(i):return {(i,):1}
def C(c):return {():c} if c else {}
def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return {m:c for m,c in out.items() if c}
def row(label,p):
    need(all(type(c) is int and len(m)<=2 for m,c in p.items()),'quadratic integer residual '+label)
    return dict(label=label,terms=terms(p))
def remap_terms(raw,mapping):return terms({tuple(sorted(mapping[i] for i in m)):c for m,c in poly(raw).items()})
def remap_guard(old,mapping):
    new=deepcopy(old);new.pop('auxiliary',None);new.pop('row',None)
    new['expression']=remap_terms(new['expression'],mapping)
    if 'coordinate' in new:new['coordinate']=mapping[new['coordinate']]
    if 'pair' in new:new['pair']=[mapping[i] for i in new['pair']]
    return new
def authenticate():
    pins=load(HERE/'SOURCE_PINS.json');need(digest(ORDINARY/'MANIFEST.json')==ORDINARY_SEAL and digest(PARENT/'source.json')==PARENT_SHA,'exact reviewed mathematical and literal parents')
    for name,h in pins['files'].items():need(digest(ROOT/name)==h,'whole source-only input '+name)
    ordinary=load(ORDINARY/'MANIFEST.json')['files'];need(set(ordinary)=={str(p.relative_to(ORDINARY)) for p in ORDINARY.rglob('*') if p.is_file() and p!=ORDINARY/'MANIFEST.json'},'closed complete ordinary design')
    for n,h in ordinary.items():need(digest(ORDINARY/n)==h,'whole ordinary design member '+n)
    expected=set(load(ORDINARY/'SOURCE_PINS.json')['files'])|{str(p.relative_to(ROOT)) for p in ORDINARY.rglob('*') if p.is_file()};need(set(pins['files'])==expected,'closed exact source-only input inventory')
def produce():
    authenticate();old=load(PARENT/'source.json');cert=load(PARENT/'transform_certificate.json');raw=load(RAW)
    need(len(old['variables'])==522 and old['domain']=='unrestricted integers','exact starting body chart')
    names={v['name']:i for i,v in enumerate(old['variables'])};need(len(names)==len(old['variables']),'unique old names')
    budget=cert['square_budget'];calls=budget['power_calls'];seeds=[];deleted=set(range(418,434));private=set(range(495,510))|{511}
    for entry in raw['seeds']:
        pair=[names[raw['variables'][token[1]]['name']] for token in entry['pair']]
        ids=[i for i,p in enumerate(raw['powers']) if p['exponent']==entry['exponent']];need(ids,'every original target has a power call')
        prefix=old['variables'][pair[0]]['name'].split('.')[0];target=calls[ids[0]]['exponent']
        seeds.append(dict(prefix=prefix,pair=pair,target=target,calls=ids))
        for suffix in ['index_at_most_Y','norm3','S_mod_U','R_mod_4Y']:
            matches=[i for i,r in enumerate(old['residuals']) if r['label']==prefix+'.'+suffix];need(len(matches)==1,'one private index row '+prefix+suffix);ri=matches[0];deleted.add(ri)
            if suffix=='index_at_most_Y':continue
            candidates=[m[0] for c,m in old['residuals'][ri]['terms'] if c==-1 and ((len(m)==2 and m[0]==m[1]) if suffix=='norm3' else len(m)==1) and old['variables'][m[0]]['kind']=='gate'];need(len(candidates)==1,'private comparison gate')
            coordinate=candidates[0];private.add(coordinate);definitions=[i for i,r in enumerate(old['residuals']) if r['label']=='multiplication' and [1,[coordinate]] in r['terms']];need(len(definitions)==1,'one private gate definition');deleted.add(definitions[0])
        private|={i for i,v in enumerate(old['variables']) if v['name'] in {prefix+'.'+s for s in ['S','R','YminusK','Squotient','Rquotient']}}
    need(len(seeds)==15 and {p['prefix'] for p in seeds}=={'index'+str(i) for i in range(16) if i!=4},'complete undoubled independent seed set')
    escapes=[(i,j) for i,r in enumerate(old['residuals']) if i not in deleted|{434} for j in private if any(j in m for c,m in r['terms'])];need(not escapes,'complete old private comparison/product nonescape')
    slots=['X','Y','AY','Y2','S','R','BR','Squotient','Rquotient','pool_quotient','lower.a','lower.b','lower.c','bound.a','bound.b','bound.c']
    variables=deepcopy(old['variables'])+[dict(name='index_cap.'+s,kind='signed_cap_witness') for s in slots]
    X,Y,AY,Y2,S,R,BR,g,r,h,la,lb,lc,ba,bb,bc=range(522,538)
    sq=lambda i:mul(V(i),V(i))
    cap=[row('index_cap.AY',add(V(AY),neg(mul(V(246),V(Y))))),row('index_cap.norm',add(sq(X),sq(Y),neg(sq(AY)),C(-1))),row('index_cap.Y2',add(V(Y2),neg(sq(Y)))),row('index_cap.BR',add(V(BR),neg(V(R)),neg(mul(V(255),V(R))))),row('index_cap.comparison_norm',add(sq(S),sq(R),neg(sq(BR)),C(-1))),row('index_cap.S_mod_U',add(V(S),neg(V(X)),neg(mul(V(250),V(g))))),row('index_cap.R_mod_4Y',add(V(R),neg(V(245)),neg(mul(C(4),mul(V(Y),V(r))))))]
    lower=add(V(Y),neg(V(245)));bound=add(sq(Y),C(-1),*[neg(sq(s['pair'][1])) for s in seeds]);pool=add(*[mul(add(V(s['pair'][1]),neg(poly(s['target']))),add(V(s['pair'][1]),neg(poly(s['target'])))) for s in seeds],sq(Y),sq(245),neg(mul(C(2),mul(V(Y),V(245)))),neg(mul(V(246),V(h))),V(h))
    graph=lambda p,a,b,c:add(p,neg(sq(a)),neg(sq(b)),neg(sq(c)),neg(V(c)))
    cap += [row('index_cap.lower_guard',graph(lower,la,lb,lc)),row('index_cap.square_bound_guard',graph(bound,ba,bb,bc)),row('index_cap.joint_residue',pool)]
    cap_guards=[dict(kind='cap_lower',expression=terms(lower),auxiliary=[la,lb,lc],label='index_cap.lower_guard'),dict(kind='cap_square_bound',expression=terms(bound),auxiliary=[ba,bb,bc],label='index_cap.square_bound_guard')]
    selected=set(cert['selected_calls']);need(selected=={3,5,7,8,9,10,11,12,13,14,15,16,17},'exact original squared-output set')
    rows=[];row_map=[]
    for i,original in enumerate(old['residuals']):
        if i in deleted:row_map.append(dict(old_row=i,status='deleted_private',new_row=None));continue
        new=deepcopy(original);status='retained'
        if i==434:new=row('shared_index.V_positive_cap_square',add(V(251),neg(V(Y2)),neg(mul(V(Y2),V(510)))));status='new_cap_product'
        for call in selected:
            if original['label']!=f'pow{call}.power_congruence':continue
            output=poly(calls[call]['output']);need(len(output)==1 and next(iter(output.values()))==1 and len(next(iter(output)))==1,'single actual output coordinate');m=next(iter(output))[0];p=poly(new['terms']);need(p.get((m,m))==-1 and (m,) not in p,'literal selected output square');new=row(new['label'],add(p,{(m,m):1},neg(V(m))));status='restored_linear_output'
        row_map.append(dict(old_row=i,status=status,new_row=len(rows)));rows.append(new)
        if i==209:rows.extend(cap)
    omitted={246,261,278};retained=[(i,g) for i,g in enumerate(cert['guards']) if g.get('coordinate') not in omitted]
    need(not any(j in private for _,gg in retained for c,m in gg['expression'] for j in m),'deleted comparison coordinates do not escape into retained guards')
    used={j for rr in rows for c,m in rr['terms'] for j in m}|{j for _,gg in retained for c,m in gg['expression'] for j in m};mapping={j:i for i,j in enumerate(sorted(used))}
    compact_rows=[dict(label=rr['label'],terms=remap_terms(rr['terms'],mapping)) for rr in rows]
    packet=dict(schema='signed_pell_joint_cap_body_v1',domain='unrestricted integers',variant='original_undoubled_targets_joint_signed_cap_source_only',variables=[variables[j] for j in sorted(used)],residuals=compact_rows,polynomial='sum of squares of all residuals',parent_source_sha256=PARENT_SHA,ordinary_manifest_sha256=ORDINARY_SEAL)
    guarded=deepcopy(packet);domain=[]
    for original_index,old_guard in retained:
        spec=remap_guard(old_guard,mapping);a,b,c=range(len(guarded['variables']),len(guarded['variables'])+3);guarded['variables'] += [dict(name=f'guard{original_index}.{s}',kind='integer_guard') for s in ['a','b','c']]
        spec.update(original_guard_index=original_index,auxiliary=[a,b,c],row=len(guarded['residuals']));guarded['residuals'].append(row('domain_guard.'+str(original_index),graph(poly(spec['expression']),a,b,c)));domain.append(spec)
    for cap_guard in cap_guards:
        spec=deepcopy(cap_guard);label=spec.pop('label');spec['expression']=remap_terms(spec['expression'],mapping);spec['auxiliary']=[mapping[j] for j in spec['auxiliary']];spec['row']=next(i for i,rr in enumerate(compact_rows) if rr['label']==label);domain.append(spec)
    plan=dict(schema='source_only_signed_cap_literal_map_v1',old_source_sha256=PARENT_SHA,ordinary_manifest_sha256=ORDINARY_SEAL,complete_old_row_map=row_map,deleted_private_coordinates=sorted(private),omitted_scalar_guards=sorted(omitted),raw_to_body=[[j,i] for j,i in mapping.items()],unused_raw_coordinates=sorted(set(range(len(variables)))-used),all_original_seeds=seeds,retained_guard_indices=[i for i,g in retained],cap_reserved_raw_slots={s:522+i for i,s in enumerate(slots)},frame_row_old=445,frame_variable_old=245,semantic_body_pointwise_preserved=False,semantic_front_rows_preserved=list(range(202)),witness_transfer='Reconstruct fresh complete Pell/cap/guard witnesses at the unchanged semantic front. No pointwise old full-body or old selected-Pell identity is claimed.',source_only=True,optimizer_executed=False,factorization_executed=False,projection_executed=False,accepted_frontier_claim=False)
    return {'source.json':packet,'guarded.json':guarded,'domain.json':dict(schema='signed_cap_source_domain_graphs_v1',guards=domain),'TRANSFORM.json':plan}
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');parser.add_argument('--output',type=Path,default=HERE);args=parser.parse_args();artifacts=produce()
    for name,value in artifacts.items():
        blob=encode(value);p=args.output/name
        if args.check:need(p.read_bytes()==blob,'whole deterministic source-only artifact '+name)
        else:
            need(not p.exists() or p.read_bytes()==blob,'refuse changed source-only artifact '+name);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(blob)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_only=True,generated={n:sha256(encode(d)).hexdigest() for n,d in artifacts.items()},optimizer_or_parent_program_executed=False,source_equivalence_or_frontier_accepted=False),indent=2,sort_keys=True))
if __name__=='__main__':main()
