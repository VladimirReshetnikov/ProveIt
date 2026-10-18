#!/usr/bin/env python3
"""Finite screen only: delete pulse255 while allowing a changed B(1) spare count.

This is not a universal proof or a claimed machine construction. A survivor
must subsequently satisfy unbounded local contracts and a complete blank boot.
"""
from pathlib import Path
import argparse
import json
import time

ROOT = Path(__file__).resolve().parent

def read(path):
    tab = {}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q,a,w,d,r=line.split()
        tab[int(q),int(a)]=(int(w),1 if d=='R' else -1,int(r))
    return tab

def encode(values, selected, marker=-1):
    ones={marker}
    h=0
    for i,v in enumerate(values):
        ones.update(range(h+1+(i==selected),h+v+2))
        h+=v+2
    return ones

def decode(ones,start):
    if {p for p in ones if p < start}!={-1}:
        return None
    p=start
    values=[]
    end=max(ones)
    while p<=end:
        if p in ones:return None
        p+=1
        if p not in ones:return None
        n=0
        while p in ones:n+=1;p+=1
        values.append(n-1)
    return values

def run(tab, values, selected, op, bound=5000):
    tape=encode(values,selected)
    wanted=values[:9].copy()
    if op=='inc':
        wanted[selected]+=1
        q,target,start=73,48,0
    elif values[selected]==0:
        q,target,start=95,112,0
    else:
        wanted[selected]-=1
        q,target,start=95,48,1
    head=0
    for steps in range(1,bound+1):
        row=tab.get((q,int(head in tape)))
        if row is None:return None
        w,d,q=row
        if w:tape.add(head)
        else:tape.discard(head)
        head+=d
        if abs(head)>4096:return None
        if q==target and head==start-1:
            # Positive decrement adds a new header one at position zero.
            if start:
                if 0 not in tape:return None
                tape.remove(0)
            result=decode(tape,start)
            if result is None or result[:9]!=wanted or len(result)<10:return None
            spares=result[9:]
            if any(x!=1 for x in spares):return None
            return steps,len(spares)
    return None

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--output',type=Path,default=Path('flexible_spares_results.json'))
    args=ap.parse_args()
    base=read(args.table)
    states=sorted({q for q,a in base}-{255})
    base={k:v for k,v in base.items() if k[0]!=255}
    tests=[([0]*9+[1]*n,r,op) for n,r,op in [(1,0,'zero'),(1,0,'inc'),(2,8,'zero'),(2,8,'inc')]]
    tests += [(v+[1]*n,r,'inc') for n in (1,2,5) for r in (0,2,8) for v in ([0]*9,list(range(9)),[2]*9)]
    tests += [(v+[1]*n,r,'zero') for n in (1,2,5) for r in (0,2,8) for v in ([0]*9,list(range(9)),[2]*9)]
    cases=[]
    started=time.monotonic()
    tested=0
    for w in (0,1):
      for d in (-1,1):
       for dest in states:
        tab=dict(base)
        tab[75,0]=(w,d,dest)
        outcomes=[]
        for values,r,op in tests:
            answer=run(tab,values,r,op)
            if answer is None:break
            outcomes.append(answer)
        tested+=1
        if len(outcomes)==len(tests):
            cases.append({'replacement':[75,0,w,'L' if d<0 else 'R',dest], 'cases':len(tests),'spare_counts':outcomes})
    out={'status':'FINITE_SCREEN','deleted':255,'tested':tested,'control_cases':len(tests),'survivors':cases,'seconds':time.monotonic()-started,'scope':'Only same macro exits and primary values, with nonempty all-B(1) spare suffix; spare count may change. No unbounded proof.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
