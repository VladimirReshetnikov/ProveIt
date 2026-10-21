#!/usr/bin/env python3
"""Finite open-associativity e-graph exported to shared-grammar search."""
import argparse,json,functools,time
from pathlib import Path
from model import *
ap=argparse.ArgumentParser();ap.add_argument('--rounds',type=int,default=2);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--input',type=Path,default=BASE/'sites218.json');a=ap.parse_args();a.output.mkdir(exist_ok=True,parents=True)
rows=json.loads(a.input.read_text());tree=parse(rows);sigs=[];ids={};prods=[];bounds=[];leaves_by_id={}
def intern_sig(g):
 if g in ids:return ids[g]
 q=len(sigs);ids[g]=q;sigs.append(g);prods.append(set())
 br=max([-x//2 for _,_,ts in g for x in ts if x< -1 and x%2==0]+[0]);co=max([(-x-1)//2 for _,_,ts in g for x in ts if x< -1 and x%2]+[0]);bounds.append((br,co));return q
@functools.lru_cache(None)
def pair_sig(a,b):
 aa,bb=sigs[a],sigs[b];la=len(aa)
 def tr(q,side):
  if q>=0:return q+(la if side else 0)
  if side==0:
   if q==-1:return la
   if q%2==0:return -1 if q==-2 else q+2
   return q
  if q< -1 and q%2:return 0 if q==-3 else q+2
  return q
 return tuple((o,r,tuple(tr(q,0)for q in ts))for o,r,ts in aa)+tuple((o,r,tuple(tr(q,1)for q in ts))for o,r,ts in bb)
def pair(a,b):
 q=intern_sig(pair_sig(a,b));prods[q].add((a,b));return q
def intern(n):
 if leaf(n):q=intern_sig(localg(n));leaves_by_id[q]=n;return q
 return pair(intern(n[0]),intern(n[1]))
root=intern(tree);base=set(range(len(sigs)));start=time.monotonic()
for r in range(a.rounds):
 snapshot=[tuple(ps)for ps in prods]
 for q,ps in enumerate(snapshot):
  for x,y in ps:
   for xx,xy in snapshot[x]:
    if bounds[xx][0]==0 and bounds[y][1]==0:
     yy=pair(xy,y);assert pair(xx,yy)==q
   for yx,yy in snapshot[y]:
    if bounds[x][0]==0 and bounds[yy][1]==0:
     xx=pair(x,yx);assert pair(xx,yy)==q
 print('round',r+1,'classes',len(sigs),'productions',sum(map(len,prods)),'sec',time.monotonic()-start,flush=True)
order=sorted(range(len(sigs)),key=lambda j:(len(sigs[j]),j));mp={x:i for i,x in enumerate(order)}
with (a.output/'model.txt').open('w')as f:
 atoms=sorted(mp[x]for x in leaves_by_id);base_closed=sorted(mp[x]for x in base if x not in leaves_by_id);req=[mp[root]]
 f.write(f'{len(sigs)} {len(atoms)} {len(base_closed)} {len(req)}\n');f.write(' '.join(map(str,atoms))+'\n');f.write(' '.join(map(str,base_closed))+'\n');f.write(' '.join(map(str,req))+'\n')
 for j in order:
  ps=sorted((mp[x],mp[y])for x,y in prods[j]);f.write(str(len(ps))+' '+' '.join(f'{x} {y}'for x,y in ps)+'\n')
(a.output/'model.json').write_text(json.dumps({'leaves':{mp[j]:n for j,n in leaves_by_id.items()},'productions':[[[mp[x],mp[y]]for x,y in sorted(prods[j])]for j in order],'root':mp[root],'base':base_closed,'source':str(a.input),'rounds':a.rounds},separators=(',',':'))+'\n')
print('exported',len(sigs),'classes',flush=True)
