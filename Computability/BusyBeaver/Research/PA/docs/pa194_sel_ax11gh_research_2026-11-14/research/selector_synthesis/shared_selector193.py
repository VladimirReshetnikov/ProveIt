#!/usr/bin/env python3
"""Try two history pairs sharing one selector using a current-cell tag.

Four old controls become three controls. A positive result would require
all simultaneous local obligations and ordinary redirects to pass.
"""
from pathlib import Path
import itertools,json,time
from synthesize_selector import parse,encode
HERE=Path(__file__).resolve().parent
def run(rows,q,hist,x,goal,maxsteps=31):
 cells=[hist,x];pos=0
 for k in range(1,maxsteps+1):
  if pos not in(-1,0) or (q,cells[pos+1])not in rows:return None
  w,d,q=rows[q,cells[pos+1]];cells[pos+1]=w;pos+=d
  if(q,pos,cells)==goal:return k
 return None
def main():
 old=parse(HERE/'primary.native.tm');states={q for q,b in old}
 pairsets=[((12,38),(127,124)),((12,38),(301,88)),((127,124),(301,88))]
 total=0;hits=[];configs=0;t0=time.monotonic()
 for pairs in pairsets:
  for reverse in itertools.product((False,True),repeat=2):
   # Each pair remains labeled by incoming0, incoming1 for the goals;
   # the checkpoint representative can be either original control.
   keeps=[p[int(v)]for p,v in zip(pairs,reverse)]
   drops=[p[1-int(v)]for p,v in zip(pairs,reverse)]
   for selector in drops:
    removed=next(q for q in drops if q!=selector)
    alias={d:k for d,k in zip(drops,keeps)}
    rho=lambda q:alias.get(q,q)
    for tag0 in(0,1):
     configs+=1
     rows={(q,b):(w,d,rho(n))for(q,b),(w,d,n)in old.items()if q!=removed}
     for i,k in enumerate(keeps):rows[k,0]=(tag0^i,-1,selector)
     goals=[]
     for i,p in enumerate(pairs):
      for hist,q in enumerate(p):
       w,d,n=old[q,0];goals.append((keeps[i],hist,(rho(n),d,[hist,w])))
     available=states-{removed}
     for p0 in available:
      rows[selector,0]=(0,1,p0)
      for p1 in available:
       rows[selector,1]=(1,1,p1);total+=1
       durations=[]
       for q,h,goal in goals:
        k=run(rows,q,h,0,goal)
        if k is None:break
        durations.append(k)
       else:
        assert all(run(rows,keeps[i],hist,1,(rho(old[q,1][2]),old[q,1][1],[hist,old[q,1][0]]))==1 for i,p in enumerate(pairs)for hist,q in enumerate(p))
        hit=dict(pairs=pairs,keeps=keeps,selector=selector,removed=removed,tag0=tag0,p0=p0,p1=p1,durations=durations)
        hits.append(hit);out=HERE/'shared193_hits';out.mkdir(exist_ok=True)
        (out/f'hit{len(hits)}.tm').write_text(encode(rows));print(hit,flush=True)
 summary=dict(family='two old binary-history pairs, current read-zero cell tags pair, one shared history selector',
              local_window=[-1,0],maxsteps=31,configurations=configs,provider_assignments=total,hits=hits,seconds=time.monotonic()-t0)
 (HERE/'shared_selector193.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
