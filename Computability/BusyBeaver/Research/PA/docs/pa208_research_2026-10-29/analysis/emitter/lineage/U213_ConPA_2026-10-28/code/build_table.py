#!/usr/bin/env python3
"""Deterministic table reconstruction; no optimizer or external dependency."""
import argparse,hashlib,json
from pathlib import Path

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def parse(raw):
    T={};start=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):start.append(int(line[9:]));continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        need(q>=0 and z>=0 and b in (0,1)and w in (0,1)and d in ('L','R'),'row domain')
        need((q,b)not in T,'duplicate row');T[q,b]=(w,1 if d=='R'else-1,z)
    need(start==[0],'start');return T
def encode(T):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode('ascii')
def validate(T,count,halt=254):
    Q={q for q,b in T};need(len(Q)==count,'state count')
    need(set(T)=={(q,b)for q in Q for b in(0,1)},'incomplete table')
    need(0 in Q and halt not in Q,'start/halt')
    need({z for w,d,z in T.values()}-Q=={halt},'target closure')
    seen={0};todo=[0]
    for q in todo:
        for b in(0,1):
            z=T[q,b][2]
            if z!=halt and z not in seen:seen.add(z);todo.append(z)
    need(seen==Q,'graph-unreachable working state')
    return Q
def build(baseline,recipe_path,out):
    raw=baseline.read_bytes();recipe=json.load(open(recipe_path))
    need(sha(raw)==recipe['baseline_sha256'],'baseline digest')
    T=parse(raw);validate(T,218)
    rows=recipe['changed_rows'];need(len(rows)==73 and len({tuple(x[:2])for x in rows})==73,'patch census')
    for q,b,w,d,z in rows:need((q,b)in T,'new row');T[q,b]=(w,d,z)
    removed=recipe['removed_states'];need(removed==[50,500,501,502,503],'removed-state census')
    T={k:v for k,v in T.items()if k[0]not in removed};Q=validate(T,213)
    need(T[34,0]==(0,-1,75)and T[146,0]==(0,1,182),'critical entries')
    raw=encode(T);need(sha(raw)==recipe['native_sha256'],'native digest')
    mapping={q:i for i,q in enumerate(sorted(Q))};mapping[254]=213
    inverse={z:q for q,z in mapping.items()};need(len(inverse)==214,'nonbijective relabeling')
    D={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in T.items()};validate(D,213,213)
    need({(inverse[q],b):(w,d,inverse[z])for(q,b),(w,d,z)in D.items()}==T,'inverse relabeling')
    dense=encode(D);need(sha(dense)==recipe['dense_sha256'],'dense digest')
    out.mkdir(parents=True,exist_ok=True)
    (out/'u213.native.tm').write_bytes(raw);(out/'u213.tm').write_bytes(dense)
    state_map={'native_to_dense':{str(k):v for k,v in mapping.items()},'dense_to_native':{str(k):v for k,v in inverse.items()},'native_halt':254,'dense_halt':213,'start':0}
    (out/'state_map.json').write_text(json.dumps(state_map,indent=2)+'\n')
    summary={'status':'EXACT_213_TABLE_RECONSTRUCTION_PASS','working_states':213,'transition_rows':426,'start':0,'halt':213,'native_halt':254,'symbols':[0,1],'tapes':1,'moves':['L','R'],'initial_tape':'all zeros','all_working_states_graph_reachable':True,'relabeling_bijection_checked':True,'changed_retained_rows_from_U218':73,'removed_native_states':removed,'native_sha256':sha(raw),'dense_sha256':sha(dense)}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');return summary
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('baseline',type=Path);p.add_argument('recipe',type=Path);p.add_argument('output',type=Path);a=p.parse_args();print(json.dumps(build(a.baseline,a.recipe,a.output),indent=2))
