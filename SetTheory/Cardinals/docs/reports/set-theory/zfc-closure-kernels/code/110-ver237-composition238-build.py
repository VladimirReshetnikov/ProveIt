#!/usr/bin/env python3
"""Reconstruct the exact238 table through two independently stored recipes.

Outputs go only to --output. The archived inputs and accepted tables are read-only.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = '909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08'
INHERITED_SHA = '069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def read(p):
    rows = {}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,n = line.split()
        q,b,w,n = map(int,(q,b,w,n))
        assert (q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R')
        rows[q,b] = (w,d,n)
    return rows

def encode(rows,start):
    return ('#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {d} {n}\n' for (q,b),(w,d,n) in sorted(rows.items()))).encode()

def main():
    if not __debug__ or sys.flags.optimize: raise RuntimeError('Assertions must be enabled')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    out=args.output.resolve()
    assert out != ROOT and ROOT not in out.parents, 'Choose output outside the archived package'
    out.mkdir(parents=True,exist_ok=True)
    boundary=ROOT/'reference/boundary239_old.tm'
    baseline=ROOT/'reference/rotation240_old.tm'
    assert sha(boundary)=='d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719'
    assert sha(baseline)=='547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f'
    old=read(boundary)
    assert len(old)==478
    assert [(q,b) for (q,b),(_,_,n) in old.items() if n==169]==[(147,0)]
    assert old[147,0]==(0,'R',169) and old[80,0]==(0,'R',25) and old[91,1]==(0,'L',50)
    new={key:value for key,value in old.items() if key[0]!=169}
    new.update({(147,0):(0,'R',80),(80,0):(0,'L',106),(91,1):(1,'L',167)})
    # Second construction: complete explicit43-row patch of the original240.
    full=read(baseline)
    recipe=json.loads((ROOT/'reference/row_edits_from_rotation240.json').read_text())
    assert recipe['deleted_states']==[169,218] and len(recipe['retained_row_edits'])==43
    for q in recipe['deleted_states']:
        del full[q,0]; del full[q,1]
    for row in recipe['retained_row_edits']:
        key=(row['state'],row['read'])
        assert full[key]==tuple(row['old'])
        full[key]=tuple(row['new'])
    assert full==new, 'Construction routes disagree'
    states={q for q,_ in new}
    assert len(states)==238 and len(new)==476
    assert set(new)=={(q,b) for q in states for b in (0,1)}
    assert {n for _,_,n in new.values()}-states=={254}
    reachable=set();todo=[95]
    while todo:
        q=todo.pop()
        if q in reachable: continue
        reachable.add(q)
        if q!=254: todo.extend(new[q,b][2] for b in (0,1))
    assert reachable==states|{254}
    order=[95]+sorted(states-{95})
    mapping={q:i for i,q in enumerate(order)}|{254:238}
    canonical={(mapping[q],b):(w,d,mapping[n]) for (q,b),(w,d,n) in new.items()}
    inherited_bytes=encode(new,95);canonical_bytes=encode(canonical,0)
    assert hashlib.sha256(inherited_bytes).hexdigest()==INHERITED_SHA
    assert hashlib.sha256(canonical_bytes).hexdigest()==CANONICAL_SHA
    assert inherited_bytes==(ROOT/'machines/zfc_composed238_old.tm').read_bytes()
    assert canonical_bytes==(ROOT/'machines/zfc_composed238.tm').read_bytes()
    renumbering=json.loads((ROOT/'machines/renumbering.json').read_text())
    assert {int(k):v for k,v in renumbering['old_to_new'].items()}==mapping
    assert renumbering['new_to_old']==order+[254]
    assert mapping[96]==84
    (out/'zfc_composed238_old.tm').write_bytes(inherited_bytes)
    (out/'zfc_composed238.tm').write_bytes(canonical_bytes)
    record={'status':'EXACT_TWO_RECIPE_CONSTRUCTION_PASS','working_states':238,'rows':476,
            'start':0,'dispatcher':84,'halt':238,'all_states_graph_reachable':True,
            'deleted_from_original240':[169,218],'changed_retained_rows_from_original240':43,
            'canonical_sha256':CANONICAL_SHA,'inherited_sha256':INHERITED_SHA,
            'builder_sha256':sha(Path(__file__)),
            'scope':'Exact construction, literal census and action-preserving relabeling; semantic proof is separate.'}
    (out/'construction.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__': main()
