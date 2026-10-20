#!/usr/bin/env python3
"""Independent interval certificate checker for the K225 guarded source graph.
The finite source-graph builder is imported from the independently retained
K225 checker. This checker does not execute the data certificate as code.
"""
from pathlib import Path
import sys,json,hashlib
D=Path(__file__).resolve().parent;P=Path('/workspace/scratch/124301573bd6/source_work/portable')
sys.path.insert(0,str(P/'verification'));import check225 as source
S,G,E=source.source(P/'results/sites225.json');C=json.loads((D/'abstract_registers.json').read_text());F=C['states'];INF=C['infinity'];cap=C['cap'];seed=[3,0,0,0,3,0,0,0,0]
def subset(a,b):return all(bl<=al and (bh==INF or ah!=INF and ah<=bh)for(al,ah),(bl,bh)in zip(a,b))
def succ(i,f):
 op,r,outs=G[i]
 if op=='CH':return []
 if op=='CD':
  lo,hi=f[r];edges=[]
  if hi>0:
   a=list(f);a[r]=(max(1,lo)-1,INF if hi==INF else hi-1);edges.append((outs[0],a))
  if lo==0:
   a=list(f);a[r]=(0,0);edges.append((outs[1],a))
  return edges
 if op=='CI':
  a=list(f);lo,hi=f[r];a[r]=(min(cap,lo+1),INF if hi>=cap else hi+1);return[(outs[0],a)]
 return[(outs[0],f)]
def check(facts):
 assert len(facts)==len(S)
 for f in facts:
  if f is None:continue
  assert len(f)==9 and all(0<=lo<=cap and (hi==INF or lo<=hi<=cap)for lo,hi in f)
 assert facts[E]is not None and subset([(n,n)for n in seed],facts[E])
 edges=0
 for i,f in enumerate(facts):
  if f is None:continue
  for j,g in succ(i,f):
   assert facts[j]is not None and subset(g,facts[j]),('noninductive',i,j)
   edges+=1
 return edges
edges=check(F);guards=[]
for i,(pc,op,r)in enumerate(S):
 if op=='CD'and F[i]is not None:
  lo,hi=F[i][r]
  if hi==0 or lo>0:guards.append([i,pc,r,'zero'if hi==0 else'positive'])
controls=[]
for i,pc,r,guard in guards:
 bad=json.loads(json.dumps(F));bad[i][r]=[1,1]
 try:check(bad)
 except AssertionError as ex:controls.append({'site':i,'rejected':True,'reason':str(ex)})
 else:raise AssertionError('negative control accepted')
rec={'status':'INDEPENDENT_SOURCE_INTERVAL_INVARIANT_PASS','source_sha256':hashlib.sha256((P/'results/sites225.json').read_bytes()).hexdigest(),'invariant_sha256':hashlib.sha256((D/'abstract_registers.json').read_bytes()).hexdigest(),'checked_guarded_edges':edges,'source_leaves':len(S),'reachable_abstract_leaves':sum(f is not None for f in F),'impossible_guards':guards,'unreachable_leaves':[S[i]for i,f in enumerate(F)if f is None],'negative_controls':controls,'scope':'All register-machine executions from logical seed(3,0,0,0,3,0,0,0,0), by source-step induction. This is not a binary-machine state reduction.'}
(D/'register_invariant_audit.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
