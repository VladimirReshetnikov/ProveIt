#!/usr/bin/env python3
"""Reconstruct both literal machines from a fixed, pinned U218 table.
No solver, search, network, or proof-assistant executable is used.
"""
from pathlib import Path
import argparse,hashlib,json

def need(ok,why):
    if not ok:raise ValueError(why)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def parse(raw):
    t={};headers=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):headers.append(line);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        need(q>=0 and z>=0 and b in(0,1)and w in(0,1)and d in('L','R'),'invalid row')
        need((q,b)not in t,'duplicate row');t[q,b]=(w,1 if d=='R'else-1,z)
    need(headers==['#! start 0'],'invalid start header');return t

def encode(t):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode('ascii')

def validate(t,count,halt=254):
    states={q for q,b in t};need(len(states)==count,'state count differs')
    need(set(t)=={(q,b)for q in states for b in(0,1)},'incomplete table')
    need(0 in states and halt not in states,'start/halt differs')
    need({z for w,d,z in t.values()}-states=={halt},'target closure differs')
    reached={0};todo=[0]
    for q in todo:
        for b in(0,1):
            z=t[q,b][2]
            if z!=halt and z not in reached:reached.add(z);todo.append(z)
    need(reached==states,'unreachable working state in graph census')
    return states

def write_pair(t,count,stem,out,recipe_key,recipe):
    states=validate(t,count);raw=encode(t)
    need(hashlib.sha256(raw).hexdigest()==recipe[recipe_key+'_native_sha256'],'native hash differs')
    name='u217_reentry'if stem=='u217'else stem
    (out/(name+'.native.tm')).write_bytes(raw)
    mapping={q:i for i,q in enumerate(sorted(states))};mapping[254]=count
    dense={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in t.items()};validate(dense,count,count)
    inv={v:k for k,v in mapping.items()}
    need({(inv[q],b):(w,d,inv[z])for(q,b),(w,d,z)in dense.items()}==t,'relabeling is not a literal bijection')
    raw=encode(dense);need(hashlib.sha256(raw).hexdigest()==recipe[recipe_key+'_dense_sha256'],'dense hash differs')
    (out/(name+'.tm')).write_bytes(raw)
    result={'native_to_dense':{str(k):v for k,v in mapping.items()},'dense_to_native':{str(v):k for k,v in mapping.items()},'native_halt':254,'dense_halt':count,'start':0}
    (out/(stem+'_state_map.json')).write_text(json.dumps(result,indent=2)+'\n')

def build(baseline,source,recipe_path,out):
    recipe=json.loads(recipe_path.read_text())
    need(sha(baseline)==recipe['baseline_sha256'],'wrong primary U218 input')
    need(sha(source)==recipe['source_sha256'],'wrong source input')
    old=parse(baseline.read_bytes());validate(old,218)
    rows=recipe['changed_rows'];need(len(rows)==74 and len({tuple(x[:2])for x in rows})==len(rows),'wrong patch census')
    need(recipe['removed_baseline_states']==[177,500,503],'wrong removed states')
    role=dict(old)
    for q,b,w,d,z in rows:
        need(b in(0,1)and w in(0,1)and d in(-1,1),'invalid patch row')
        role[q,b]=(w,d,z)
    role={k:v for k,v in role.items()if k[0]not in recipe['removed_baseline_states']};validate(role,215)
    raw=encode(role);need(hashlib.sha256(raw).hexdigest()==recipe['role215_sha256'],'wrong intermediate bytes')
    out.mkdir(parents=True,exist_ok=True);(out/'role215.native.tm').write_bytes(raw)
    need(recipe['fold214']=={'removed':156,'representative':182},'wrong fold')
    final={(q,b):(w,d,182 if z==156 else z)for(q,b),(w,d,z)in role.items()if q!=156}
    write_pair(final,214,'u214',out,'u214',recipe)
    need(recipe['reentry217']=={'removed':112,'representative':134},'wrong companion fold')
    companion={(q,b):(w,d,134 if z==112 else z)for(q,b),(w,d,z)in old.items()if q!=112}
    write_pair(companion,217,'u217',out,'u217',recipe)
    return {'status':'EXACT_MACHINES_RECONSTRUCTED','primary_states':214,'primary_rows':428,'companion_states':217,'companion_rows':434,'source_sha256':sha(source),'role215_sha256':recipe['role215_sha256'],'u214_native_sha256':recipe['u214_native_sha256'],'u214_dense_sha256':recipe['u214_dense_sha256'],'u217_native_sha256':recipe['u217_native_sha256'],'u217_dense_sha256':recipe['u217_dense_sha256'],'all_working_states_graph_reachable':True,'dense_relabeling_is_bijective':True}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('baseline',type=Path);p.add_argument('source',type=Path);p.add_argument('recipe',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    print(json.dumps(build(a.baseline,a.source,a.recipe,a.output),indent=2))
