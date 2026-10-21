#!/usr/bin/env python3
"""Check the optional 26/0 -> 194 engine route; not part of final GC215."""
from pathlib import Path
import argparse,hashlib,json

def read(raw):
    T={};start=None
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):start=int(line[9:]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        if (q,b) in T or b not in (0,1) or w not in (0,1) or d not in ('L','R'):raise ValueError('Invalid row')
        T[q,b]=(w,1 if d=='R'else -1,z)
    if start!=0:raise ValueError('Expected start0')
    return T

def step(T,q,h,t):
    if h not in t:raise ValueError('Read outside certified local cells')
    w,d,z=T[q,t[h]];t=dict(t);t[h]=w
    return z,h+d,t

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--table',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();raw=a.table.read_bytes();T=read(raw)
    assert {k:v for k,v in T.items() if v[2]==26}=={(11,0):(0,-1,26)}
    assert T[26,0]==(0,1,134) and T[26,1]==(1,1,38)
    assert T[134,0]==T[194,0]==(0,1,17)
    N=dict(T);N[26,0]=(0,1,194)
    blocks=[]
    for b in (0,1):
        initial=(26,0,{0:b,1:0});old=initial;new=initial;steps=2 if b==0 else 1
        for _ in range(steps):
            old=step(T,*old);new=step(N,*new)
        assert old==new
        assert old[2]==initial[2]
        blocks.append(dict(read=b,right_marker=0,old_steps=steps,new_steps=steps,
                           final_state=old[0],head_delta=old[1],tape_unchanged=True))
    native=('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(N.items()))).encode()
    a.out.mkdir(parents=True,exist_ok=True);(a.out/'engine-route.native.tm').write_bytes(native)
    receipt=dict(status='OPTIONAL_ENGINE_ROUTE_PASS',parent_sha256=hashlib.sha256(raw).hexdigest(),
        variant_sha256=hashlib.sha256(native).hexdigest(),blocks=blocks,
        incoming26=[[11,0,0,-1,26]],changed_row=[26,0,0,1,194],
        scope='Halting equivalence for all initial tapes and head positions from control0. This optional variant is not the packaged GC215 table.',
        proof='Every reachable26 has right neighbor0 because its sole incoming row11/0 writes0 and moves left. On read0, the old two-step route26->134->17 and new26->194->17 agree exactly. On read1 the unchanged row exits to38. All other rows agree. Positive-block induction applies.',
        allocation_note='This discharges the engine constraint on134/0 arising from26. Other uses of134/0, including decoder uses, still require their own allocation and runtime checks.',
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (a.out/'engine-route.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
