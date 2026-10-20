#!/usr/bin/env python3
"""Breadth-diverse safe reassociation search, with per-layer DAG compaction.

This is discovery only: every reported improvement is independently checked by
both pinned primitive-CFG implementations, so heuristic hash collisions could
only lose a search opportunity, never certify an incorrect source.
"""
from pathlib import Path
from functools import lru_cache
import argparse,json,time,random,sys
from zero5_search import Dag,s
from environment import BASE_SOURCE

class Hdag(Dag):
 def __init__(self):
  super().__init__();self.hashes=[]
 def add(self,n):
  old=self.index.get(n)
  if old is not None:return old
  i=super().add(n)
  self.hashes.append(hash((0,*n)) if isinstance(n[0],str) else hash((1,self.hashes[n[0]],self.hashes[n[1]])))
  return i

def compact(d,front):
 nd=Hdag()
 @lru_cache(None)
 def f(q):
  return nd.add(d.nodes[q] if d.leaf(q) else tuple(f(c) for c in d.nodes[q]))
 return nd,[f(q) for q in front]

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--quota',type=int,default=100);ap.add_argument('--steps',type=int,default=40);ap.add_argument('--maxdag',type=int,default=208);ap.add_argument('--target',type=int,default=205);ap.add_argument('--seed',type=int,default=219205);ap.add_argument('--source',type=Path,default=BASE_SOURCE);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
 random.seed(a.seed);rows=json.loads(a.source.read_text());old=s.tree(rows);graph=s.graph_intervals(rows)
 d=Hdag();root=d.intern(old);front=[root];seen={d.hashes[root]};best=len(d.reach(root));start=time.monotonic();improvements=[]
 for depth in range(a.steps):
  buckets={n:[] for n in range(a.target,a.maxdag+1)};generated=0
  for cur in front:
   for q in d.reach(cur):
    for nq,direction in d.rotations(q):
     new=d.replace(cur,q,nq);h=d.hashes[new]
     if h in seen:continue
     seen.add(h);generated+=1
     if d.zero[new]>6:continue
     n=len(d.reach(new))
     if n>a.maxdag:continue
     if n<best:
      t=d.tree(new);ss=s.sites(t)
      assert s.graph_intervals(ss)==graph and s.graph_arithmetic(ss)[0]==graph
      name=f'best_n{n}_d{depth+1}'
      (a.out/(name+'.sites.json')).write_bytes(s.compact(ss))
      rec={'name':name,'dag':n,'search_depth':depth+1,'metrics':s.metrics(t),'source_cfg_identical':True,'seconds':time.monotonic()-start}
      (a.out/(name+'.json')).write_text(json.dumps(rec,indent=2)+'\n');improvements.append(rec);best=n
      print('BEST',rec,flush=True)
      if n<=a.target:return
     if n in buckets:buckets[n].append((random.random(),new))
  front=[]
  counts={}
  for n,c in buckets.items():
   c.sort();chosen=c[:a.quota];front.extend(q for _,q in chosen);counts[n]=(len(c),len(chosen))
  interned=len(d.nodes);d,front=compact(d,front)
  rec={'depth':depth+1,'frontier':len(front),'buckets':counts,'seen':len(seen),'interned_before':interned,'interned_after':len(d.nodes),'best':best,'seconds':round(time.monotonic()-start,2)}
  print('DEPTH',json.dumps(rec),flush=True)
  (a.out/'summary.json').write_text(json.dumps({'last':rec,'improvements':improvements},indent=2)+'\n')
  if not front:break
if __name__=='__main__':main()
