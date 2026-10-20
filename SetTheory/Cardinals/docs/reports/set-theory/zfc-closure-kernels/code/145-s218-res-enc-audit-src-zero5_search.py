#!/usr/bin/env python3
"""Search safe ordered-pair reassociations for source zero-run5.
General safe rule ((A,B),C)<->(A,(B,C)) with no escaping break from A
and no escaping continue from C. Candidates require separate compilation.
"""
from pathlib import Path
from functools import lru_cache
import argparse,json,time,sys,random
from environment import P, BASE_SOURCE, s
class Dag:
 def __init__(self):self.nodes=[];self.index={};self.bound=[];self.leading=[];self.zero=[];self.viol=[];self.depth=[]
 def add(self,n):
  if n in self.index:return self.index[n]
  i=len(self.nodes);self.nodes.append(n);self.index[n]=i
  if isinstance(n[0],str):
   op,a=n;self.bound.append((1,0)if op=='CD'else(a,0)if op=='CB'else(0,a)if op=='CC'else(0,0));self.leading.append(0);self.zero.append(0);self.viol.append(0);self.depth.append(0)
  else:
   a,b=n;x,y=self.bound[a],self.bound[b];L=1+self.leading[a]
   self.bound.append((max(x[0]-1,y[0],0),max(x[1],y[1]-1,0)));self.leading.append(L);self.zero.append(max(L,self.zero[a],self.zero[b]));self.viol.append(self.viol[a]+self.viol[b]+int(L>=6));self.depth.append(1+max(self.depth[a],self.depth[b]))
  return i
 def intern(self,t):return self.add(t if s.leaf(t)else tuple(self.intern(c)for c in t))
 def leaf(self,i):return isinstance(self.nodes[i][0],str)
 def reach(self,i):
  seen=set();todo=[i]
  while todo:
   q=todo.pop()
   if q in seen:continue
   seen.add(q)
   if not self.leaf(q):todo.extend(self.nodes[q])
  return seen
 def tree(self,i):
  @lru_cache(None)
  def f(q):return self.nodes[q]if self.leaf(q)else tuple(f(c)for c in self.nodes[q])
  return f(i)
 def replace(self,root,old,new):
  @lru_cache(None)
  def f(q):return new if q==old else q if self.leaf(q)else self.add(tuple(f(c)for c in self.nodes[q]))
  return f(root)
 def rotations(self,q):
  if self.leaf(q):return
  a,c=self.nodes[q]
  if not self.leaf(a):
   aa,b=self.nodes[a]
   if self.bound[aa][0]==0 and self.bound[c][1]==0:yield self.add((aa,self.add((b,c)))), 'right'
  a,bc=self.nodes[q]
  if not self.leaf(bc):
   b,c=self.nodes[bc]
   if self.bound[a][0]==0 and self.bound[c][1]==0:yield self.add((self.add((a,b)),c)), 'left'

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=BASE_SOURCE);ap.add_argument('--seed',type=int,default=219005);ap.add_argument('--beam',type=int,default=100);ap.add_argument('--steps',type=int,default=25);ap.add_argument('--maxdag',type=int,default=208);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
 random.seed(a.seed);rows=json.loads(a.source.read_text());old=s.tree(rows);graph=s.graph_intervals(rows)
 d=Dag();root=d.intern(old);front=[root];seen={root};trails={root:[]};best=(d.viol[root],len(d.reach(root)));start=time.monotonic();summaries=[]
 for depth in range(a.steps):
  candidates=[]
  for cur in front:
   R=d.reach(cur)
   for q in R:
    for nq,direction in d.rotations(q):
     new=d.replace(cur,q,nq)
     if new in seen:continue
     seen.add(new);n=len(d.reach(new));v=d.viol[new]
     if n>a.maxdag:continue
     candidates.append((v,n,random.random(),new));trails[new]=trails[cur]+[(q,nq,direction)]
     if(v,n)<best:
      best=v,n;t=d.tree(new);ss=s.sites(t)
      assert s.graph_intervals(ss)==graph and s.graph_arithmetic(ss)[0]==graph
      name=f'best_v{v}_n{n}_d{depth+1}'
      (a.out/(name+'.sites.json')).write_bytes(s.compact(ss))
      rec={'name':name,'violations':v,'dag':n,'depth':depth+1,'trails':trails[new],'metrics':s.metrics(t),'source_cfg_identical':True}
      (a.out/(name+'.json')).write_text(json.dumps(rec,indent=2)+'\n');summaries.append(rec)
      print('BEST',rec,'seconds',round(time.monotonic()-start,1),flush=True)
  candidates.sort();front=[x[3]for x in candidates[:a.beam]]
  print('DEPTH',depth+1,'frontier',len(front),'seen',len(seen),'interned',len(d.nodes),'best',best,'seconds',round(time.monotonic()-start,1),flush=True)
  (a.out/'summary.json').write_text(json.dumps({'best':best,'steps':depth+1,'seen':len(seen),'seconds':time.monotonic()-start,'improvements':summaries},indent=2)+'\n')
  if not front or best[0]==0:break
if __name__=='__main__':main()
