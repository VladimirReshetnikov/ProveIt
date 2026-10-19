#!/usr/bin/env python3
"""Exact free-tape proof of the 169->80 fold with 91/1 compensation.

Unspecified cells are independent symbolic variables. This proof does not
sample their values. The separate selector-guard check supplies the single
nonstructural assumption: state169 reading1 sees another1 to its right.
"""
from pathlib import Path
import argparse, hashlib, json

def table(path):
    out={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,z=line.split(); key=int(q),int(b)
        assert key not in out
        out[key]=int(w),1 if d=='R' else -1,int(z)
    return out

def symbolic_run(tab,q,tape,steps):
    h=0; tape=dict(tape);trace=[]
    for _ in range(steps):
        read=tape.get(h,('free',h));assert read in (0,1),('unconstrained read',q,h,read)
        w,d,z=tab[q,read];trace.append({'state':q,'head':h,'read':read,'write':w,'direction':d,'next':z})
        tape[h]=w;h+=d;q=z
    return q,h,tape,trace

def equivalent(a,b):
    qa,ha,ta,_=a;qb,hb,tb,_=b
    return qa==qb and ha==hb and all(ta.get(i,('free',i))==tb.get(i,('free',i))for i in set(ta)|set(tb))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();old=table(args.baseline);new=table(args.candidate)
    assert len(old)==480 and len(new)==478
    expected={k:(w,d,80 if z==169 else z)for k,(w,d,z)in old.items()if k[0]!=169}
    expected[80,0]=(0,-1,106);expected[91,1]=(1,-1,167)
    assert new==expected
    # These old-machine predicates are preserved by every incoming row.
    structural={67:{-1:0},80:{-2:0,-1:1},91:{-3:0,-2:1,-1:1},169:{-1:0}}
    preservation=[]
    for (q,b),(w,d,z) in sorted(old.items()):
        if z not in structural: continue
        source=dict(structural.get(q,{}))
        if 0 in source and source[0]!=b: continue
        source[0]=b;after=source.copy();after[0]=w
        for offset,value in structural[z].items():
            assert after.get(d+offset)==value,('structural implication failed',q,b,z,offset)
        preservation.append({'source':[q,b],'target':z})
    assert 95 not in structural
    specs=[
      ('80/read0',80,{-1:1,0:0},1,5),
      ('80/read1',80,{0:1},1,1),
      ('169/read0',169,{-1:0,0:0},1,3),
      ('169/read1',169,{-1:0,0:1,1:1},1,5),
      ('91/read0',91,{0:0},1,1),
      ('91/read1',91,{-3:0,-2:1,-1:1,0:1},3,11),
    ]
    proofs=[]
    for name,q,assumptions,oldsteps,newsteps in specs:
        a=symbolic_run(old,q,assumptions,oldsteps);b=symbolic_run(new,80 if q==169 else q,assumptions,newsteps)
        mapped=(80 if a[0]==169 else a[0],*a[1:]);assert equivalent(mapped,b),(name,a,b)
        proofs.append({'name':name,'old_state':q,'new_state':80 if q==169 else q,'assumptions':assumptions,'all_other_cells':'independent free variables, never inspected unless forced by listed assumptions','old_steps':oldsteps,'new_steps':newsteps,'endpoint_state':a[0],'endpoint_head':a[1],'old_trace':a[3],'new_trace':b[3]})
    receipt={'status':'EXACT_SYMBOLIC_LOCAL_PASS','baseline_sha256':hashlib.sha256(args.baseline.read_bytes()).hexdigest(),'candidate_sha256':hashlib.sha256(args.candidate.read_bytes()).hexdigest(),'working_states':239,'deleted':169,'retained':80,'structural_invariant':structural,'structural_preservation_rows':preservation,'semantic_guard_required':'In reachable old configurations: q=169 and tape[h]=1 implies tape[h+1]=1.','semantic_guard_proved_here':False,'maximum_old_block':3,'maximum_new_block':11,'cases':proofs,'theorem_scope':'Under the stated invariant and guard, the state map169->80 has positive-block simulation for arbitrary exterior tapes. All other old transitions agree in one step; all halt endpoints are unchanged.'}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items()if k not in ('cases','structural_invariant','structural_preservation_rows')},indent=2))

if __name__=='__main__':main()
