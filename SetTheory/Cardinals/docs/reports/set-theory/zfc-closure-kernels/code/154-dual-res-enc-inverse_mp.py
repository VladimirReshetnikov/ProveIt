#!/usr/bin/env python3
"""Inverse detachment exploration, source semantics and compiler costs.
This first version accepts all four constructor tags; logical calibration is separate.
"""
from functools import cache
from pathlib import Path
import itertools,json
import encoding_support as x
s,b,z=x.s,x.b,x.z
W=x.W
OUT=W/'inverse_mp';OUT.mkdir(exist_ok=True)
ROWS=json.loads((W/'K220_Construction_2026-10-20/machine/sites220.json').read_text())
TREE=s.tree(ROWS)
T=b.read_table((W/'K220_Construction_2026-10-20/machine/k220.native.tm').read_bytes())
get=lambda lo,hi:s.subtree(TREE,x.at_interval(TREE,lo,hi))
oldmp=get(4652,4744)
unpair=get(4678,4686)
ubody=unpair[1]
compare=get(4708,4718)
move65=get(4621,4624)
move16=get(4705,4708)
move61=get(4730,4733)
clear1=('CD',1),('CC',1)
clear7=('CD',7),('CC',1)
move71=('CD',7),(('CI',1),('CC',2))
CI=lambda r:('CI',r)
CD=lambda r:('CD',r)
CC=lambda k:('CC',k)
CB=lambda k:('CB',k)
seq=z.seq

@cache
def assocs(xs):
 if len(xs)==1:return (xs[0],)
 return tuple((a,b)for i in range(1,len(xs))for a in assocs(xs[:i])for b in assocs(xs[i:]))

def sim(n,regs,cap=200000):
 rr=s.sites((n,('CH',None)));g=s.graph_arithmetic(rr)[0]
 assert g==s.graph_intervals(rr)
 R=list(regs);pc=0
 for st in range(cap):
  (op,*ar),js=g[pc]
  if op=='halt':return R,st
  if op=='increment':R[ar[0]]+=1;pc=js[0]
  elif op=='decrement':
   nz=R[ar[0]]>0
   if nz:R[ar[0]]-=1
   pc=js[nz]
  else:pc=js[0]
 raise RuntimeError('simulation cap')

def unp(n):
 a=b=0
 for _ in range(n):
  b+=1
  if a:a-=1
  else:a,b=b,0
 return a,b

def check_unp(n):
 for h in range(65):
  rr=[3,4,5,0,6,h,0,0,7]
  try:out,st=sim(n,rr,50000)
  except RuntimeError:return False
  exp=rr.copy();exp[5]=0;exp[6],exp[7]=unp(h//4)
  if out!=exp:return False
 return True



def index(h):
 return h//4 if h%4!=1 else max(0,h//4-1)


def check_mp(n):
 checks=0
 for h in range(160):
  a,bb=unp(index(h))
  for tw in sorted(set((0,1,2,3,4,5,a,a+1))):
   rr=[3,tw,5,0,6,h,0,0,7]
   out,st=sim(n,rr)
   exp=rr.copy();exp[1]=bb if tw==a else 0;exp[5]=exp[6]=exp[7]=0
   assert out==exp, (h,tw,out,exp)
   checks+=1
 return checks


def measure():
 tests=((CD(5),(CD(5),CD(5))),CD(5))
 approx=tests,ubody
 decode=CD(5),(CD(5),approx)
 for h in range(1500):
  rr=[3,4,5,0,6,h,0,0,7]
  out,st=sim(decode,rr)
  exp=rr.copy();exp[5]=0;exp[6],exp[7]=unp(index(h))
  assert out==exp,(h,out,exp)
 (OUT/'decode_sites.json').write_bytes(s.compact(s.sites(decode)))
 (OUT/'decode_graph.json').write_text(json.dumps(s.graph_arithmetic(s.sites((decode,('CH',None))))[0],indent=2)+'\n')
 results=[]
 core=compare,move71
 for i,n in enumerate(assocs((decode,move65,move16,core,clear7))):
  checks=check_mp(n)
  tt=s.replace(TREE,'1111',n);rr=s.sites(tt)
  assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
  rec={'variant':i,'source_metrics':s.metrics(tt),'mp_metrics':s.metrics(n),'checked_small_mp_inputs':checks,'semantic_status':'NEW ENUMERATOR: separate equivalence and runtime proof required'}
  d=OUT/f'v{i}';d.mkdir(exist_ok=True)
  (d/'sites.json').write_bytes(s.compact(rr))
  try:
   U,m=z.compile_tree(T,TREE,tt);rec['compiler']=m
   (d/'candidate.tm').write_bytes(b.table_bytes(U))
  except Exception as exc:rec['error']=repr(exc)
  (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');results.append(rec)
  print(json.dumps(rec),flush=True)
 (OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':
 measure()
