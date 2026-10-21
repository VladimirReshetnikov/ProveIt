#!/usr/bin/env python3
"""Local open-control reassociation with exact escaping control outcomes.

Source optimization only. Every saved candidate is independently checked
against both complete guarded ordinal graph resolvers before compilation.
"""
from pathlib import Path
from functools import cache
import sys,json,itertools,time,hashlib,collections,argparse,random
import control_rotation219 as q
s,b,old,T,G=q.s,q.b,q.old,q.T,q.G
ROOT=q.ROOT
@cache
def local(t):
 rows=s.sites(t);intervals={}
 def visit(n,p='',lo=0):
  hi=lo+q.width(n);intervals[p]=(lo,hi)
  if not s.leaf(n):visit(n[0],p+'0',lo);visit(n[1],p+'1',lo+q.width(n[0]))
 visit(t);N=len(rows)
 def target(p,edge,k):
  for j in range(len(p)-1,-1,-1):
   if p[j]==edge:
    k-=1
    if k==0:
     x=intervals[p[:j]][1 if edge=='0'else 0]
     return('N',0)if x==N else('pc',x)
  return('B'if edge=='0'else'C',k)
 graph=[];opts=[]
 for i,(p,op,arg)in enumerate(rows):
  after=('pc',i+1)if i+1<N else('N',0)
  if op=='CI':goal=(op,arg,after)
  elif op=='CD':goal=(op,arg,target(p,'0',1),after)
  elif op=='CH':goal=(op,)
  else:goal=('identity',target(p,'0'if op=='CB'else'1',arg))
  graph.append(goal)
  opts.append({(typ,k):target(p,edge,k)for typ,edge,ks in[('CB','0',[1]),('CC','1',[1,2,3])]for k in ks})
 return rows,graph,opts
@cache
def rotated(x,direction,mode):
 if s.leaf(x[direction]):return None
 if direction==0:(a,bb),cc=x;y=(a,(bb,cc))
 else:a,(bb,cc)=x;y=((a,bb),cc)
 if not s.boundary(a)[0]and not s.boundary(cc)[1]:return y,[]
 xr,xg,_=local(x);yr,yg,opts=local(y);changes=[]
 for i,(before,after)in enumerate(zip(xg,yg)):
  if before[0]!='identity':
   if before!=after:return None
  else:
   chs=[op for op,t in opts[i].items()if t==before[1]]
   if not chs:return None
   cur=tuple(yr[i][1:]);choice=cur if cur in chs else min(chs,key=lambda z:(z[0]!=cur[0],z[1]))
   if mode and len(chs)>1:choice=min(chs,key=lambda z:(z[1],z[0]))
   if choice!=cur:yr[i][1:]=choice;changes.append([i,*cur,*choice])
 new=s.tree(yr)
 assert local(new)[1]==xg
 return new,changes
@cache
def info(n):
 if s.leaf(n):return 0,0,0
 a,bb=info(n[0]),info(n[1]);lead=1+a[0]
 return lead,max(lead,a[1],bb[1]),1+max(a[2],bb[2])
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--depth',type=int,default=5);ap.add_argument('--beam',type=int,default=12);ap.add_argument('--seed',type=int,default=219218);args=ap.parse_args()
 rng=random.Random(args.seed);out=ROOT/'root_work/control_rotation_fast219';out.mkdir(exist_ok=True)
 front=[(old,[])];seen={old};best=206;records=[];hist=collections.Counter();start=time.time()
 for depth in range(args.depth):
  queue=[]
  for tr,chain in front:
   for x in q.nodes(tr):
    if s.leaf(x):continue
    for direction in(0,1):
     for mode in(0,1):
      hit=rotated(x,direction,mode)
      if hit is None:continue
      y,changes=hit;new=q.replace_all(tr,x,y)
      if new in seen:continue
      seen.add(new);nn=len(q.nodes(new));hist[nn]+=1
      if nn>best+1 or info(new)[1]>6:continue
      ch=chain+[{'direction':direction,'subtree_sha':hashlib.sha256(s.compact(x)).hexdigest(),'local_control_changes':changes}]
      queue.append((nn,rng.random(),new,ch))
      if nn<best:
       best=nn;print('NEW_SOURCE_MIN',best,'DEPTH',depth+1,'SECONDS',time.time()-start,flush=True)
      if nn<=205:
       rows=s.sites(new);assert s.graph_intervals(rows)==G;assert s.graph_arithmetic(rows)[0]==G
       key=hashlib.sha256(s.compact(rows)).hexdigest()[:16];d=out/key;d.mkdir(exist_ok=True)
       (d/'sites.json').write_bytes(s.compact(rows));rec={'key':key,'metrics':s.metrics(new),'chain':ch,'exact_CFG':True}
       try:U,cm=q.compiler.compile_tree(T,old,new);rec['compiler']=cm;(d/'candidate.tm').write_bytes(b.table_bytes(U))
       except Exception as exc:rec['error']=repr(exc)
       (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');records.append(rec)
       print(json.dumps({k:rec[k]for k in('key','metrics','compiler','error')if k in rec}),flush=True)
  queue.sort(key=lambda z:(z[0],z[1]));front=[(n,ch)for _,_,n,ch in queue[:args.beam]]
  print('ROUND',depth+1,'MIN',best,'UNIQUE',len(seen),'HIST',dict(hist),'SECONDS',round(time.time()-start,1),flush=True)
  (out/'summary.json').write_text(json.dumps({'round':depth+1,'minimum_source_DAG':best,'unique_sources':len(seen),'histogram':dict(hist),'seconds':time.time()-start,'records':records},indent=2)+'\n')
if __name__=='__main__':main()
