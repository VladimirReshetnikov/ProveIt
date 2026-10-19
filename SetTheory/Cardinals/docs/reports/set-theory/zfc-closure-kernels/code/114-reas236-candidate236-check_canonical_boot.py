#!/usr/bin/env python3
"""Validate the canonical table and independently replay its exact blank startup."""
from pathlib import Path
import hashlib,json

import sys
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Run without -O/-OO: verification assertions are required.')

HERE=Path(__file__).resolve().parent

def parse(path):
    t={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();key=int(q),int(b)
        assert key not in t and d in ('L','R')
        t[key]=int(w),d,int(z)
    return t

def expected_frame():
    # Logical seed (3,0,0,0,3,0,0,0,0) in the inherited physical order.
    physical=[0,0,0,3,0,0,3,0,0]
    ones={-6,176};cell=177
    for value in physical+[1]*167:
        cell+=1
        for _ in range(value+1):ones.add(cell);cell+=1
    assert len(ones)==351
    return ones

def main():
    canonical=HERE/'zfc_reassociate236.tm';oldlabels=HERE/'zfc_reassociate236_old.tm'
    t=parse(canonical);inherited=parse(oldlabels)
    assert set(t)=={(q,b) for q in range(236) for b in (0,1)}
    assert all(w in (0,1) and 0<=z<=236 for w,d,z in t.values())
    ren=json.loads((HERE/'renumbering.json').read_text())
    f={int(q):z for q,z in ren['old_to_new'].items()}
    assert set(f.values())==set(range(237)) and len(f)==237
    assert f[95]==0 and f[96]==84 and f[254]==236
    assert {(f[q],b):(w,d,f[z]) for (q,b),(w,d,z) in inherited.items()}==t
    reached={0};todo=[0]
    for state in todo:
        if state==236:continue
        for bit in (0,1):
            target=t[state,bit][2]
            if target not in reached:reached.add(target);todo.append(target)
    assert reached==set(range(237))
    wanted=expected_frame();ones=set();state=0;head=0;visits={};lo=hi=0
    for steps in range(3_000_001):
        if state==84 and head==-5 and ones==wanted:break
        assert state!=236 and steps<3_000_000,'did not produce the exact required seed'
        bit=int(head in ones);visits[state,bit]=visits.get((state,bit),0)+1
        write,direction,state=t[state,bit]
        if write:ones.add(head)
        else:ones.discard(head)
        head+=1 if direction=='R' else -1;lo=min(lo,head);hi=max(hi,head)
    # A separate dense tape has a different storage representation and uses
    # the exact discovered duration, checking the whole finite support.
    dense=bytearray(hi-lo+1);head2=0;state2=0
    for _ in range(steps):
        write,direction,state2=t[state2,dense[head2-lo]]
        dense[head2-lo]=write
        head2= head2+1 if direction=='R' else head2-1
    dense_ones={lo+i for i,value in enumerate(dense) if value}
    assert (state2,head2,dense_ones)==(84,-5,wanted)
    result={'status':'CANONICAL_STRUCTURE_AND_EXACT_SPARSE_DENSE_BOOT_PASS',
            'sha256':hashlib.sha256(canonical.read_bytes()).hexdigest(),
            'working_states':236,'rows':472,'start':0,'dispatcher':84,'halt':236,
            'all_working_states_graph_reachable':True,'halt_graph_reachable':True,
            'canonical_bijection_checked':True,'boot_steps':steps,'head':head,
            'marker':-6,'header':176,'logical_registers':[3,0,0,0,3,0,0,0,0],
            'spares':{'count':167,'value':1},'one_cells':351,
            'one_positions':sorted(wanted),'blank_zero_elsewhere':True,
            'visits_to_merged_state182':sum(visits.get((f[182],b),0) for b in (0,1)),
            'tape_visited_interval':[lo,hi]}
    (HERE/'canonical_boot_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='one_positions'},indent=2))

if __name__=='__main__':main()
