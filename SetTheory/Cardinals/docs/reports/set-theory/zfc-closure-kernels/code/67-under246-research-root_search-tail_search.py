#!/usr/bin/env python3
"""Search reusable increment/zero-decrement tail states. Discovery only."""
from pathlib import Path
import sys, itertools, json, time
BASE=Path(__file__).resolve().parents[1]/'sources/context246/zfc-context246'
sys.path.insert(0,str(BASE/'code'))
from rebuild_machines import build
T=build()
def blocks(vs):
    return [b for v in vs for b in [0]+[1]*(v+1)]
def cases():
    out=[]
    for vals,r in [([0,0],0),([1,0],0),([0,1],0),([1,1],0),([1,0,2],1),([2,3,0,0],2),([0,0,1,0],2),([4,3,2,0],0),([0,2,0,3],1)]:
      for mode in ['dec0','inc']:
        vs=vals.copy()
        if mode=='dec0':vs[r]=0
        inp=blocks(vs); inp[sum(v+2 for v in vs[:r])+1]=0
        # arbitrary nonblank left exterior, which must not be touched.
        left={-2,-4,-7,-8}
        one={i for i,b in enumerate(inp) if b}|left
        wantvs=vs.copy()
        if mode=='inc':wantvs[r]+=1
        out.append((mode,73 if mode=='inc' else 95,one,wantvs,left))
    return out
def validate(tab,case,limit=3000):
    mode,q,ones,want,left=case
    one=set(ones);h=0
    target=48 if mode=='inc' else 112
    seen=set()
    for t in range(limit):
      if t and q==target and h==-1:
        if {i for i in one if i<0}!=left:return None
        expect=blocks(want)
        if any((i in one)!=bool(b) for i,b in enumerate(expect)):return None
        if mode=='dec0':
          return (t,[]) if {i for i in one if i>=len(expect)}==set() else None
        p=len(expect);extra=[]
        while p<=max(one):
          if p in one or p+1 not in one:return None
          p+=1;v=0
          while p in one:p+=1;v+=1
          extra.append(v-1)
        return t,extra
      if (q,int(h in one)) not in tab:return None
      w,d,q=tab[q,int(h in one)]
      if w:one.add(h)
      else:one.discard(h)
      h+=1 if d=='R' else -1
      if h < -1:return None
    return None
def main():
    cases_=cases();candidates=[];began=time.monotonic()
    for w,d,q in itertools.product(range(2),'LR',sorted({q for q,b in T}-{255})):
      U={k:v for k,v in T.items() if k[0]!=255}
      U[75,0]=w,d,q
      result=[]
      for case in cases_:
        r=validate(U,case)
        if r is None:break
        result.append(r)
      else:
        candidates.append(dict(row=[w,d,q],results=result))
        print('CANDIDATE',candidates[-1],flush=True)
    print(json.dumps(dict(seconds=time.monotonic()-began,candidates=candidates),indent=2))
if __name__=='__main__':main()
