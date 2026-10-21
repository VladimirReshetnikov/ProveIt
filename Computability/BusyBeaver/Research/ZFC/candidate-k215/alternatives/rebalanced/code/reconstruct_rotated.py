#!/usr/bin/env python3
"""Deterministically reconstruct a K215 closed-source-rotation candidate.

This checker uses only Python's standard library and the preserved source
syntax utilities in vendor/. It checks exact ordered primitive and guarded
control-flow identity, literal decoder prefixes, the row recipe, and a dense
renaming. It does not replace the separate arbitrary-natural runtime proof.
"""
from pathlib import Path
from collections import defaultdict
import argparse,hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'vendor'))
import source_language as s
import build221 as b

BASE_TABLE='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
BASE_SOURCE='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def dump(path,data):path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
def canon(T):
    mapping={0:0};todo=[0]
    for q in todo:
        for bit in(0,1):
            target=T[q,bit][2]
            if target!=254 and target not in mapping:mapping[target]=len(mapping);todo.append(target)
    mapping[254]=len(mapping)
    rows=[(mapping[q],bit,w,d,mapping[t])for q in todo for bit in(0,1)for w,d,t in[T[q,bit]]]
    return rows,mapping
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--recipe',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    assert __debug__ and not sys.flags.optimize,'Run without -O'
    raw=(a.baseline/'k215.native.tm').read_bytes();source=(a.baseline/'sites215.json').read_bytes();assert sha(raw)==BASE_TABLE and sha(source)==BASE_SOURCE
    T=b.read_table(raw);original=dict(T);root=s.tree(json.loads(source));rows=s.sites(root);word=[r[1:]for r in rows];cfg=s.graph_intervals(rows);assert cfg==s.graph_arithmetic(rows)[0]
    recipe=json.loads(a.recipe.read_text());steps=recipe['rotations'];history=[]
    def replace(t,old,new):
        if t==old:return new
        if s.leaf(t):return t
        return replace(t[0],old,new),replace(t[1],old,new)
    for j,item in enumerate(steps):
        q,m,direction=item['q'],item['m'],item['direction'];side=int(direction=='left');assert direction in('left','right')
        groups,paths=b.decoder_map(T,root);assert len(groups[q])==len(groups[m])==1
        node=next(iter(groups[q]));child=node[side];assert not s.leaf(child) and next(iter(groups[m]))==child
        assert {qq for qq,ns in groups.items()if node in ns}=={q}
        assert set(paths[m])=={p+str(side)for p in paths[q]}
        assert T[q,side]==(side,1,m) and all(T[v,bit][:2]==(bit,1)for v in(q,m)for bit in(0,1))
        A,B,C=(node[0],*node[1])if side else(*node[0],node[1]);assert all(s.boundary(x)==(0,0,False)for x in(A,B,C))
        new=((A,B),C)if side else(A,(B,C));root=replace(root,node,new);U=dict(T)
        if side:
            U[q,0]=(0,1,m);U[q,1]=(1,1,T[m,1][2]);U[m,0]=(0,1,T[q,0][2]);U[m,1]=(1,1,T[m,0][2])
        else:
            U[q,0]=(0,1,T[m,0][2]);U[q,1]=(1,1,m);U[m,0]=(0,1,T[m,1][2]);U[m,1]=(1,1,T[q,1][2])
        rows=s.sites(root);assert [r[1:]for r in rows]==word and s.graph_intervals(rows)==cfg==s.graph_arithmetic(rows)[0]
        b.decoder_map(U,root)
        history.append({'index':j,'q':q,'m':m,'direction':direction,'source_occurrences':len(paths[q]),'source_paths':paths[q],'factor_leaf_counts':[len(s.sites(x))for x in(A,B,C)],'closed_factors':True,'changed_rows':[[*key,*U[key]]for key in sorted(U)if U[key]!=T[key]]})
        T=U
    assert len(T)==430 and len({q for q,_ in T})==215
    src=s.compact(rows);native=b.table_bytes(T)
    if 'expected_native_sha256'in recipe:assert sha(native)==recipe['expected_native_sha256']
    if 'expected_source_sha256'in recipe:assert sha(src)==recipe['expected_source_sha256']
    dense,mapping=canon(T);assert len(mapping)==216 and mapping[0]==0 and mapping[254]==215
    densebytes=('#! start 0\n'+''.join(f'{q} {bit} {w} {"R"if d==1 else"L"} {z}\n'for q,bit,w,d,z in dense)).encode('ascii')
    paths_before=[r[0]for r in json.loads(source)];paths_after=[r[0]for r in rows]
    groups,prefixes=b.decoder_map(T,root)
    result={'status':'DETERMINISTIC_RECONSTRUCTION_PASS','scope':'Exact source word/CFG, literal decoder prefixes, row recipe, dense naming. The full runtime and blank startup are separate certificates.','parent_native_sha256':BASE_TABLE,'parent_source_sha256':BASE_SOURCE,'native_sha256':sha(native),'dense_sha256':sha(densebytes),'source_sha256':sha(src),'working_states':215,'rows':430,'source_metrics':s.metrics(root),'ordered_primitive_word_equal':True,'both_guarded_CFGs_equal':True,'guarded_cases':sum(2 if op=='CD'else 1 for _,op,arg in rows),'internal_prefixes':sum(map(len,prefixes.values())),'not_a_state_renaming':canon(original)[0]!=dense,'changed_rows':[[*key,*T[key]]for key in sorted(T)if T[key]!=original[key]],'address_statistics':{'old_sum':sum(map(len,paths_before)),'new_sum':sum(map(len,paths_after)),'shorter':sum(len(v)<len(u)for u,v in zip(paths_before,paths_after)),'same':sum(len(v)==len(u)for u,v in zip(paths_before,paths_after)),'longer':sum(len(v)>len(u)for u,v in zip(paths_before,paths_after))},'rotations':history}
    a.output.mkdir(parents=True,exist_ok=False);(a.output/'candidate.native.tm').write_bytes(native);(a.output/'candidate.tm').write_bytes(densebytes);(a.output/'sites.json').write_bytes(src);dump(a.output/'canonicalization.json',{'native_to_dense':mapping,'start_native':0,'start_dense':0,'halt_native':254,'halt_dense':215,'dispatcher_native':84,'dispatcher_dense':mapping[84]});dump(a.output/'construction.json',result);dump(a.output/'recipe.json',recipe)
    print(json.dumps({k:v for k,v in result.items()if k not in('rotations','changed_rows')},indent=2))
if __name__=='__main__':main()
