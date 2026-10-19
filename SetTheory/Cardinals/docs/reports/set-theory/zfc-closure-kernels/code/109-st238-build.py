#!/usr/bin/env python3
"""Reconstruct the exact 238-state table from the pinned Boundary239 input."""
from pathlib import Path
import argparse, hashlib, json, sys

ROOT=Path(__file__).resolve().parent
OLD_SHA='d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719'
NEW_SHA='069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c'
CANON_SHA='909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08'

def require(ok,message):
    if not ok:raise ValueError(message)

def parse(path):
    table={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        fields=line.split();require(len(fields)==5,'Malformed row')
        q,b,w,d,t=fields;q,b,w,t=map(int,(q,b,w,t))
        require(b in (0,1) and w in (0,1) and d in ('L','R'),'Bad action')
        require((q,b) not in table,'Duplicate row')
        table[q,b]=(w,d,t)
    states={q for q,b in table}
    require(set(table)=={(q,b) for q in states for b in (0,1)},'Incomplete table')
    require({t for w,d,t in table.values()}-states=={254},'Unexpected halt')
    return table

def serialize(table,start):
    return ('#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {d} {t}\n' for(q,b),(w,d,t) in sorted(table.items()))).encode('ascii')

def main():
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Run without -O/-OO.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    source=ROOT/'inputs/boundary239_old.tm'
    require(hashlib.sha256(source.read_bytes()).hexdigest()==OLD_SHA,'Wrong baseline bytes')
    old=parse(source);require(len(old)==478,'Expected 239-state baseline')
    require(sorted((q,b) for(q,b),(_,_,t) in old.items() if t==169)==[(147,0)],'Incoming edge changed')
    phi=lambda q:80 if q==169 else q
    new={(q,b):(w,d,phi(t)) for(q,b),(w,d,t) in old.items() if q!=169}
    new[80,0]=(0,'L',106);new[91,1]=(1,'L',167)
    changed=[(q,b) for q,b in sorted(new) if old[q,b]!=new[q,b]]
    require(changed==[(80,0),(91,1),(147,0)],'Wrong edit set')
    states={q for q,b in new};require(len(states)==238 and len(new)==476,'Wrong state count')
    require({t for w,d,t in new.values()}-states=={254},'Dangling target')
    order=[95]+sorted(states-{95});ren={q:i for i,q in enumerate(order)}|{254:238}
    canonical={(ren[q],b):(w,d,ren[t]) for(q,b),(w,d,t) in new.items()}
    raw=serialize(new,95);canon=serialize(canonical,0)
    require(hashlib.sha256(raw).hexdigest()==NEW_SHA,'Inherited table digest mismatch')
    require(hashlib.sha256(canon).hexdigest()==CANON_SHA,'Canonical table digest mismatch')
    reached={95};todo=[95]
    while todo:
        q=todo.pop()
        if q==254:continue
        for b in (0,1):
            t=new[q,b][2]
            if t not in reached:reached.add(t);todo.append(t)
    require(reached==states|{254},'A listed state is graph-unreachable')
    a.out.mkdir(parents=True,exist_ok=True)
    (a.out/'zfc238_old.tm').write_bytes(raw);(a.out/'zfc238.tm').write_bytes(canon)
    (a.out/'renumbering.json').write_text(json.dumps({'old_to_canonical':ren,'canonical_to_old':{v:k for k,v in ren.items()}},indent=2)+'\n')
    record={'status':'PASS_EXACT_238_CONSTRUCTION','working_states':238,'transition_rows':476,'start':0,'dispatcher':ren[96],'halt':238,'head':0,'initial_tape':'all zero on the integers','symbols':[0,1],'moves':['L','R'],'initialization_included':True,'parent_state_count':239,'deleted_from_parent':169,'both_deleted_from_rotation240':[169,218],'retained_rows_changed':[{'row':[q,b],'old':old[q,b],'new':new[q,b]}for q,b in changed],'unchanged_retained_rows':473,'graph_reachable_working_states':238,'baseline_sha256':OLD_SHA,'old_label_sha256':NEW_SHA,'canonical_sha256':CANON_SHA,'scope':'Exact finite table construction and bijective relabeling. Runtime and logical calibration are separate proof obligations.'}
    (a.out/'construction.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__':main()
