#!/usr/bin/env python3
"""Exhaust a two-control history-selector family with arbitrary exterior tape.

This is a same-count redesign search, not a claimed state reduction.
"""
import itertools, json, sys, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
def parse(p):
 r={}
 for line in p.read_text().splitlines():
  if not line.strip() or line.startswith('#'):continue
  q,b,w,d,n=line.split();r[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
 return r
def encode(rows):
 return ''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n'for(q,b),(w,d,n)in sorted(rows.items()))
def run(rows,q,hbit,x,goal,limit=15):
 cells=[hbit,x];pos=0
 for k in range(1,limit+1):
  if pos not in (-1,0) or q==254:return None
  w,d,q=rows[q,cells[pos+1]];cells[pos+1]=w;pos+=d
  if(q,pos,cells)==goal:return k
 return None
def main():
 old=parse(HERE/'primary.native.tm');states=sorted({q for q,b in old})
 incoming={q:set()for q in states}
 for(q,b),(w,d,n)in old.items():
  if n in incoming:incoming[n].add((w,d))
 ls=[q for q in states if incoming[q]=={(0,1)} and q!=74]
 rs=[q for q in states if incoming[q]=={(1,1)} and q!=74]
 hits=[];tested=0;t0=time.monotonic()
 for left in ls:
  for right in rs:
   equal=[b for b in(0,1)if old[left,b]==old[right,b]]
   if len(equal)!=1:continue
   common=equal[0];different=1-common
   for keep,selector in [(left,right),(right,left)]:
    rho=lambda q:keep if q==selector else q
    new={(rho(q),b):(w,d,rho(n))for(q,b),(w,d,n)in old.items()if q!=selector}
    new[keep,different]=(different,-1,selector)
    goals=[]
    for q,h in((left,0),(right,1)):
     w,d,n=old[q,different];goals.append((rho(n),d,[h,w]))
    for p0 in states:
     new[selector,0]=(0,1,p0)
     for p1 in states:
      new[selector,1]=(1,1,p1);tested+=1
      k0=run(new,keep,0,different,goals[0])
      if k0 is None:continue
      k1=run(new,keep,1,different,goals[1])
      if k1 is None:continue
      # Recheck the common cases on the final joint table as well.
      for q,h in((left,0),(right,1)):
       w,d,n=old[q,common]
       assert run(new,keep,h,common,(rho(n),d,[h,w]))==1
      out=HERE/'selector_hits';out.mkdir(exist_ok=True)
      name=f'l{left}_r{right}_k{keep}_s{selector}_p{p0}_{p1}'
      (out/(name+'.tm')).write_text(encode(new))
      hit=dict(name=name,left=left,right=right,keep=keep,selector=selector,p0=p0,p1=p1,
               common=common,durations=[k0,k1],changed_rows=sum(old[k]!=v for k,v in new.items()))
      hits.append(hit);print(json.dumps(hit),flush=True)
 summary=dict(family='two-control history selector, one common branch, returning providers preserve history',
              test_limit=15,tests=tested,hits=hits,seconds=time.monotonic()-t0)
 (HERE/'selector_search.json').write_text(json.dumps(summary,indent=2)+'\n')
 print('SUMMARY',tested,len(hits),summary['seconds'],flush=True)
if __name__=='__main__':main()
