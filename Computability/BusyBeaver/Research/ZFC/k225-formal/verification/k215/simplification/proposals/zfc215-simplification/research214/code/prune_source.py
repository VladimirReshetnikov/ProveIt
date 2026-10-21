#!/usr/bin/env python3
import json,sys,hashlib
if not __debug__: raise RuntimeError('Run with assertions enabled, without -O.')
from pathlib import Path
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
W=args.output;W.mkdir(exist_ok=True,parents=True)
R=Path(__file__).resolve().parents[1]/'inputs'
sys.path.insert(0,str(Path(__file__).resolve().parent/'vendor'))
import source_language as s
import source_splice as sp
rows=json.load(open(R/'sites215.json'));G=s.graph_intervals(rows);inv=json.load(open(Path(__file__).resolve().parents[1]/'results/abstract_source_k2.json'));I=inv['invariants'];impossible=set(map(tuple,inv['unreachable_cases']))
oldtree=s.tree([[p,'CI',0]for p,o,a in rows])
# Preserve old ordinal tags during pruning.
idx={p:i for i,(p,o,a)in enumerate(rows)}
def tagged(p=''):
 if p in idx:return idx[p]
 return tagged(p+'0'),tagged(p+'1')
def prune(t,delset):
 if isinstance(t,int):return None if t in delset else t
 a,b=[prune(z,delset)for z in t]
 return b if a is None else a if b is None else(a,b)
def sites(t,p=''):
 if isinstance(t,int):return[(t,p)]
 return sites(t[0],p+'0')+sites(t[1],p+'1')
def trial(deleted,name):
 tr=prune(tagged(),deleted);tag=sites(tr);mp={i:j for j,(i,p)in enumerate(tag)};new=[[p,*rows[i][1:]]for i,p in tag]
 def skip(i):
  seen=set()
  while i in deleted:
   assert i not in seen;seen.add(i)
   assert i in(4671,4733),('entered impossible deleted site',i)
   assert rows[i][1]=='CD' and I[i][rows[i][2]]==1
   i=G[i][1][0]
  return mp[i]
 def targets(i):return [skip(j)for j in G[i][1]]
 # Update control depths only when required by removed tree structure.
 ranges={}
 for j,(i,p)in enumerate(tag):
  for n in range(len(p)+1):
   z=p[:n]
   if z not in ranges:ranges[z]=[j,j+1]
   else:ranges[z][1]=j+1
 def target(p,op,k):
  bit='0'if op=='CB'else'1'
  for n in range(len(p)-1,-1,-1):
   if p[n]==bit:
    k-=1
    if k==0:return ranges[p[:n]][int(op=='CB')]%len(tag)
  return 0
 edits=[]
 for j,(i,p)in enumerate(tag):
  op,a=rows[i][1:]
  if op not in('CB','CC'):continue
  wanted=targets(i)
  # At most path depth and one root-wrap level.
  found=[]
  for k in range(1,len(p)+2):
   if [target(p,op,k)]==wanted:found.append(k)
  assert found,(i,p,op,a,wanted)
  k=a if a in found else min(found)
  if k!=a:edits.append([i,op,a,k])
  new[j][2]=k
 g=s.graph_intervals(new);assert g==s.graph_arithmetic(new)[0]
 for j,(i,p)in enumerate(tag):
  want=targets(i)
  for b,dest in enumerate(want):
   pos=bool(b)if rows[i][1]=='CD'else False
   if(i,pos)in impossible:continue
   assert g[j][1][b]==dest,(j,i,rows[i],g[j],want)
 newtree=s.tree(new);raw=s.compact(new);(W/f'{name}.json').write_bytes(raw)
 print(name,s.metrics(newtree),'control-depth-changes',edits,'newnodes',len(sp.nodes(newtree)-sp.nodes(s.tree(rows))))
 return {'name':name,'deleted':sorted(deleted),'source_sha256':hashlib.sha256(raw).hexdigest(),'metrics':s.metrics(newtree),'control_depth_changes':edits,'old_to_new':mp}
ans=[]
for deleted,name in [(set(range(4671,4674)),'pruned3'),(set(range(4733,4735)),'pruned2'),(set(range(4671,4674))|set(range(4733,4735)),'pruned5')]:
 ans.append(trial(deleted,name))
(W/'prune_receipt.json').write_text(json.dumps(ans,indent=2)+'\n')
