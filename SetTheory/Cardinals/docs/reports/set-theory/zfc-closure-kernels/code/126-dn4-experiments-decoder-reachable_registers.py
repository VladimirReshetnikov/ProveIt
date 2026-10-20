#!/usr/bin/env python3
"""Sound finite Cartesian value-bucket analysis of a source control graph.

This script only proposes reductions of reachable source guards. It does not
assert an exact set of reachable register valuations or alter a machine.
"""
from pathlib import Path
from collections import deque,Counter
import argparse,json,hashlib,time,sys,os
ap=argparse.ArgumentParser();ap.add_argument('sites',type=Path);ap.add_argument('--output',type=Path,required=True)
ap.add_argument('--cutoff',type=int,default=8);ap.add_argument('--modulus',type=int,default=2)
a=ap.parse_args();C,M=a.cutoff,a.modulus;assert C>=4 and M>=1;N=C+M
base=Path(os.environ['ZFC_BASELINE_PORTABLE']).resolve()/'verification'
sys.path.insert(0,str(base));import check225 as s
sites,graph,entry=s.source(a.sites)
def bucket(n):return n if n<C else C+(n%M)
def possibilities(i):return [i]if i<C else [n for n in range(C,C+2*M)if bucket(n)==i]
# Beyond the cutoff, both the boundary representative and a larger one are
# included. This matters for decrement: one may cross into the exact range.
inc=[sum(1<<j for j in {bucket(n+1)for n in possibilities(i)})for i in range(N)]
dec=[sum(1<<j for j in {bucket(n-1)for n in possibilities(i)if n>0})for i in range(N)]
def transf(mask,t):
 r=0
 for i in range(N):
  if(mask>>i)&1:r|=t[i]
 return r
facts=[None]*len(sites);seed=[3,0,0,0,3,0,0,0,0];facts[entry]=[1<<bucket(n)for n in seed]
todo=deque([entry]);queued={entry};updates=0
def outputs(i,vals):
 op,arg,successors=graph[i]
 if op=='CH':return []
 if op=='CI':
  out=vals.copy();out[arg]=transf(out[arg],inc);return [(successors[0],out)]
 if op=='CD':
  out=[]
  if vals[arg]&~1:
   val=vals.copy();val[arg]=transf(val[arg]&~1,dec);out.append((successors[0],val))
  if vals[arg]&1:
   val=vals.copy();val[arg]=1;out.append((successors[1],val))
  return out
 return [(successors[0],vals)]
tic=time.monotonic()
while todo:
 i=todo.popleft();queued.remove(i)
 for j,v in outputs(i,facts[i]):
  before=facts[j];after=v.copy()if before is None else [x|y for x,y in zip(before,v)]
  if after!=before:
   facts[j]=after;updates+=1
   if j not in queued:todo.append(j);queued.add(j)
checks=0
for i,v in enumerate(facts):
 if v is None:continue
 for j,w in outputs(i,v):
  assert facts[j]is not None and all(x&~y==0 for x,y in zip(w,facts[j]));checks+=1
dead=[i for i,v in enumerate(facts)if v is None];disabled=[]
for i,(pc,op,arg)in enumerate(sites):
 if facts[i]is None:continue
 if op=='CD':
  if not(facts[i][arg]&1):disabled.append([i,'zero'])
  if not(facts[i][arg]&~1):disabled.append([i,'positive'])
out=dict(status='INDUCTIVE_REGISTER_BUCKET_PASS',cutoff=C,modulus=M,buckets=N,
 source_sha256=hashlib.sha256(a.sites.read_bytes()).hexdigest(),source_sites=len(sites),entry=entry,
 seed=seed,dead_sites=dead,disabled_decrement_guards=disabled,facts=facts,updates=updates,closure_checks=checks,
 seconds=time.monotonic()-tic,inc_bucket_masks=inc,dec_bucket_masks=dec,
 scope='Every source configuration reachable from the calibrated seed lies in its Cartesian bucket mask. This is an overapproximation, not a reachability decision.')
a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in('facts','dead_sites','disabled_decrement_guards')},indent=2));print('dead sites',len(dead),'disabled guards',len(disabled),Counter(x[1]for x in disabled))
