#!/usr/bin/env python3
"""Finite stress checks of three exact-time symbolic identities.

The independent paper proof is by induction on arbitrary unary blocks; these
checks expose mistakes in its head coordinates, times and complete tape frames.
"""
from pathlib import Path
import argparse, hashlib, json, random, time
from check_literal_instructions import read_table

ROOT = Path(__file__).resolve().parent


def blocks(values):
    out=[]
    for v in values:out += [0]+[1]*(v+1)
    return out

def marked(values,r):
    out=blocks(values)
    out[sum(v+2 for v in values[:r])+1]=0
    return out

def paint(right,left,head):
    return {head+i for i,b in enumerate(right) if b} | {head-i-1 for i,b in enumerate(left) if b}

def execute(T,q,h,one,n):
    one=set(one);seen=set()
    for _ in range(n):
        key=q,int(h in one);seen.add(key)
        w,d,q=T[key]
        if w:one.add(h)
        else:one.discard(h)
        h+=d
    return q,h,one,seen

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--table',type=Path,default=ROOT/'machines/zfc_prefix250_old.tm')
    ap.add_argument('--output',type=Path,default=ROOT/'results/literal-macros.json')
    if not __debug__:ap.error('Assertions are required; do not use -O.')
    args=ap.parse_args();T=read_table(args.table)
    rng=random.Random(2501017);counts={'increment':0,'positive_decrement':0,'zero_decrement':0}
    used=set();steps=0;began=time.monotonic()
    for r in range(9):
        for rep in range(600):
            # Every selected primary has a following block. Some tests have a
            # single spare, others many, with arbitrary zero/nonzero contents.
            vs=[rng.randrange(0,70) for _ in range(9+rng.randrange(1,8))]
            left=[rng.randrange(2) for _ in range(rng.randrange(0,40))]
            h=rng.randrange(-30,31)
            for mode in counts:
                values=vs.copy();result=vs.copy();widthpre=sum(v+2 for v in vs[:r])
                if mode=='increment':
                    result[r]+=1;result.append(1)
                    n=2*sum(v+2 for v in values)+7
                    q=73;wantq=48;wanth=h-1;newleft=left;newh=h
                elif mode=='positive_decrement':
                    values[r]=rng.randrange(1,200);result=values.copy();result[r]-=1
                    n=2*widthpre+4
                    q=95;wantq=48;wanth=h;newleft=[1]+left;newh=h+1
                else:
                    values[r]=0;result=values.copy()
                    n=2*widthpre+7
                    q=95;wantq=112;wanth=h-1;newleft=left;newh=h
                actual=execute(T,q,h,paint(marked(values,r),left,h),n)
                want=(wantq,wanth,paint(blocks(result),newleft,newh))
                assert actual[:3]==want,(r,rep,mode,actual[:2],want[:2],sorted(actual[2]^want[2]))
                counts[mode]+=1;steps+=n;used.update(actual[3])
    pulsed = T[97,0] == (1,1,83)
    assert ((97,1) in used) == pulsed
    if pulsed: assert (97,0) not in used
    out=dict(status='PASS',finite_only=True,unbounded_proof=False,counts=counts,
             total_cases=sum(counts.values()),literal_steps=steps,
             arbitrary_left_context_samples=True,positive_values_up_to=199,
             normal_values_up_to=69,spare_lengths=list(range(1,8)),
             exact_times={'increment':'2 width(vs)+7','positive_decrement':'2 width(pre)+4','zero_decrement':'2 width(pre)+7'},
             pulse_variant=pulsed,used_97_read1=(97,1) in used,used_initializer_97_read0=(97,0) in used,seconds=time.monotonic()-began,
             table_sha256=hashlib.sha256(args.table.read_bytes()).hexdigest())
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
