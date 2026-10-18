#!/usr/bin/env python3
"""Literal regression suite for four general box lemmas, not their proof."""
from pathlib import Path
from collections import Counter
import hashlib,json,random,time
import rebuild_machines as p

def bits(values):
    out=[]
    for v in values:out.extend([0]+[1]*(v+1))
    return out

def test(T,op,r,vs,left):
    raw=bits(vs)
    if op!='mark':raw[sum(v+2 for v in vs[:r])+1]=0
    ones={i for i,b in enumerate(raw) if b}|left
    if op=='mark':
        start=(60,44,31,56,38,40,28,64,69)[r];stop=2 if r==0 else 6;headout=-1
        want=bits(vs);want[sum(v+2 for v in vs[:r])+1]=0;offset=0;newleft=left
    elif op=='inc':
        start=73;stop=48;headout=-1;values=vs.copy();values[r]+=1;values.append(1)
        want=bits(values);offset=0;newleft=left
    elif op=='dec0':
        assert vs[r]==0
        start=95;stop=112;headout=-1;want=bits(vs);offset=0;newleft=left
    else:
        assert vs[r]>0
        start=95;stop=48;headout=0;values=vs.copy();values[r]-=1
        want=bits(values);offset=1;newleft=left|{0}
    expected={i+offset for i,b in enumerate(want) if b}|newleft
    q=start;h=0;used=set()
    for tick in range(10000):
        if tick and h==headout and q==stop:
            assert ones==expected,(op,r,vs,left,tick,q,h,sorted(ones^expected))
            return tick,used
        assert h>=0,(op,r,vs,'premature left exit',tick,q,h)
        b=int(h in ones);used.add((q,b));w,d,q=T[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    raise AssertionError((op,r,vs,'fuel'))

def main():
    T=p.build();rng=random.Random(20261017);counts=Counter();used=set();maximum=0;began=time.monotonic()
    for op in ('mark','inc','dec0','decp'):
        for r in range(9):
            for sample in range(100):
                vs=[rng.randrange(8) for _ in range(9+rng.randrange(1,10))]
                if op=='dec0':vs[r]=0
                if op=='decp':vs[r]=rng.randrange(1,9)
                left={-i for i in range(1,20) if rng.randrange(2)}
                n,foot=test(T,op,r,vs,left);maximum=max(maximum,n);used|=foot;counts[op]+=1
    out=dict(status='PASS',seed=20261017,samples=dict(counts),maximum_literal_steps=maximum,
             observed_rows=sorted(used),boot_row_97_read0_absent_from_macro_traces=(97,0) not in used,
             elapsed_seconds=time.monotonic()-began,
             scope='Finite randomized literal regression checks, independent of the algebraic proofs.')
    (Path(__file__).resolve().parents[1]/'results/prefix-box-regression.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='observed_rows'},indent=2))

if __name__=='__main__':main()
