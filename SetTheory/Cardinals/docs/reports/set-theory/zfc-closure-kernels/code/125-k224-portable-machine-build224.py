#!/usr/bin/env python3
"""Reconstruct the fixed 224-state binary Turing machine and its label maps.

This builder applies a single contextual fold to the pinned Rel225 table.
Its source/theory calibration is an upstream obligation. check224.py separately
checks the exact whole-tape fold and complete blank-tape startup.
"""
from pathlib import Path
from collections import deque
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent
OLD_SHA='4526bd8cf2160ac5dfce039add0550e9788095f60ecc6b4462afd4ebbfd42790'
SOURCE_SHA='309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878'
MAP_SHA='8d77f4dcddc9966ba58b0cb8515d604334983e86b51580b546960b1e1d1a7151'
KEEP,DROP,HALT=157,191,254

def require(condition,message):
    if not condition:raise ValueError(message)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def dump(path,value):path.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
def read_table(path):
    rows={};starts=[]
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]))
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require((q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R'),'Malformed or duplicate transition')
        rows[q,b]=(w,1 if d=='R'else-1,z)
    states={q for q,b in rows}
    require(len(starts)==1 and starts[0]in states,'Invalid initial state')
    require(set(rows)=={(q,b)for q in states for b in(0,1)},'Incomplete table')
    require({z for w,d,z in rows.values()}-states=={HALT},'Unexpected terminal state')
    return rows,starts[0]
def write_table(path,rows,start):
    path.write_text(f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(rows.items())))
def canonical_map(rows,start):
    order=[start];mapping={start:0}
    for q in order:
        for b in(0,1):
            z=rows[q,b][2]
            if z!=HALT and z not in mapping:mapping[z]=len(order);order.append(z)
    require(set(order)=={q for q,b in rows},'Unreachable working state')
    mapping[HALT]=len(order)
    return mapping

def build(output):
    oldpath=ROOT/'reference/rel225.k.tm';sourcepath=ROOT/'reference/sites.json';mappath=ROOT/'reference/legacy_state_map.json'
    require(digest(oldpath)==OLD_SHA,'Pinned Rel225 input changed')
    require(digest(sourcepath)==SOURCE_SHA,'Pinned Rel source changed')
    require(digest(mappath)==MAP_SHA,'Pinned legacy map changed')
    old,start=read_table(oldpath);require(start==0 and len(old)==450,'Wrong Rel225 census')
    phi=lambda q:KEEP if q==DROP else q
    new={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in old.items()if q!=DROP}
    new[KEEP,0]=(0,-1,67);new[KEEP,1]=(1,-1,148)
    require(len(new)==448,'Wrong final census')
    output.mkdir(parents=True,exist_ok=True)
    write_table(output/'candidate224.k.tm',new,start)
    mapping=canonical_map(new,start)
    canonical={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in new.items()}
    write_table(output/'candidate224.tm',canonical,mapping[start])
    legacy={int(q):z for q,z in json.loads(mappath.read_text())['k230_to_old'].items()if int(q)in mapping};legacy[HALT]=HALT
    require(len(set(legacy.values()))==len(legacy),'Noninjective inherited map')
    legacyrows={(legacy[q],b):(w,d,legacy[z])for(q,b),(w,d,z)in new.items()}
    (output/'candidate224.legacy.tm').write_text(f'#! start {legacy[start]}\n'+''.join(f'{legacy[q]} {b} {w} {"R"if d==1 else"L"} {legacy[z]}\n'for(q,b),(w,d,z)in sorted(new.items())))
    (output/'sites.json').write_bytes(sourcepath.read_bytes())
    dump(output/'renumbering224.json',dict(k_to_canonical=mapping,canonical_to_k={v:k for k,v in mapping.items()},k_to_legacy={q:legacy[q]for q in mapping},legacy_to_canonical={legacy[q]:z for q,z in mapping.items()}))
    result=dict(status='EXACT_224_RECONSTRUCTION_PASS',working_states=224,rows=448,start=0,halt=224,
        keep_k_label=KEEP,deleted_k_label=DROP,retained_rows=[[KEEP,0,0,'L',67],[KEEP,1,1,'L',148]],
        input_table_sha256=OLD_SHA,input_source_sha256=SOURCE_SHA,source_preserved_byte_for_byte=True,
        canonical_rule='Breadth-first discovery from state0, examining read0 before read1; halt gets224.',
        artifacts={p.name:digest(p)for p in sorted(output.iterdir())if p.name in('candidate224.k.tm','candidate224.tm','candidate224.legacy.tm','sites.json','renumbering224.json')},
        scope='Literal construction and label isomorphisms only. The independent fold, blank startup, universal binary runtime, and inherited theory calibration are separate checks.')
    dump(output/'construction224.json',result);return result
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=ROOT/'results');args=ap.parse_args()
    print(json.dumps(build(args.output),indent=2))
