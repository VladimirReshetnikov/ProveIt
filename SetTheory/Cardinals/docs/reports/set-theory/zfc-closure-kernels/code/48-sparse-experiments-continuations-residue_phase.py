#!/usr/bin/env python3
"""Sound nonrelational exact-prefix + modular-tail abstract interpretation."""
from pathlib import Path
from collections import defaultdict,deque
import json,sys,time
from control_bisim import build

def analyze(M,m):
 assert M>0 and m>0 and M%m==0
 sites,cases,targets,first,*_=build()
 by=defaultdict(list)
 for i,c in enumerate(cases):by[c[0]].append(i)
 lowmask=(1<<M)-1;himask=(1<<m)-1
 def inc(mask):
  high=mask>>M
  h=((high<<1)&himask)|(high>>(m-1))|((mask>>(M-1))&1)
  return((mask<<1)&lowmask)|(h<<M)
 def dec(mask):
  high=mask>>M
  h=(high>>1)|((high&1)<<(m-1))
  low=(mask&lowmask)>>1
  if high&1:low|=1<<(M-1)
  return low|(h<<M)
 def transfer(v,c):
  _,path,op,r,z=c;out=list(v)
  if op=='CI':out[r]=inc(out[r])
  elif op=='CD':
   if z:
    if not out[r]&1:return
    out[r]=1
   else:
    if not out[r]&~1:return
    out[r]=dec(out[r]&~1)
  return tuple(out)
 values=[None]*len(sites);values[first]=(1,)*9
 work=deque([first]);inq={first};pops=0;then=time.monotonic()
 while work:
  s=work.popleft();inq.remove(s);pops+=1
  for i in by[s]:
   t=targets[i]
   if t is None:continue
   out=transfer(values[s],cases[i])
   if out is None:continue
   old=values[t];new=out if old is None else tuple(a|b for a,b in zip(old,out))
   if old!=new:
    values[t]=new
    if t not in inq:work.append(t);inq.add(t)
 excluded=[]
 for i,c in enumerate(cases):
  v=values[c[0]];out=None if v is None else transfer(v,c)
  if out is None:excluded.append(i)
  elif targets[i] is not None:
   dest=values[targets[i]]
   assert dest is not None and all(a&~b==0 for a,b in zip(out,dest))
 assert all(v&1 for v in values[first])
 result={'M':M,'modulus':m,'excluded':excluded,'excluded_details':[{ 'index':i,'case':cases[i]}for i in excluded],'pops':pops,'elapsed':time.monotonic()-then}
 print(json.dumps(result),flush=True)
 Path(__file__).with_name(f'residue-phase-{M}-{m}.json').write_text(json.dumps({**result,'masks':values},indent=2)+'\n')
 return result
if __name__=='__main__':
 for a,b in [(2,1),(8,4),(32,8),(128,32)]:analyze(a,b)
