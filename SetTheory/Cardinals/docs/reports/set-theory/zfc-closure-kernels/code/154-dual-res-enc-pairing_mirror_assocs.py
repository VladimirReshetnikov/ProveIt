#!/usr/bin/env python3
"""Exact-CFG association variants of the globally mirrored pairing routines."""
from functools import cache
import itertools,json
import pairing_mirror as p
q=p.q;s=q.s;b=q.b;z=q.z
OUT=q.W/'pairing_mirror_assocs';OUT.mkdir(exist_ok=True)

@cache
def shapes(lo,hi):
 if hi==lo+1:return (lo,)
 return tuple((l,r)for mid in range(lo+1,hi)for l in shapes(lo,mid)for r in shapes(mid,hi))

@cache
def bounds(n):
 if isinstance(n,int):return n,n+1
 return bounds(n[0])[0],bounds(n[1])[1]


def assoc_cfg(old,remap):
 word=q.x.flat(p.remap(old,remap));N=len(word)
 target=s.graph_arithmetic(s.sites((old,('CH',None))))[0][:-1]
 out=[]
 for sh in shapes(0,N):
  opts={}
  valid=True
  def visit(n,zs=(N,),ones=()):
   nonlocal valid
   if not valid:return
   if isinstance(n,int):
    op,arg=word[n];goal=target[n][1]
    if op=='CD':
     if zs[-1]!=goal[0]:valid=False
    elif op=='CB':
     if len(zs)<arg or zs[-arg]!=goal[0]:valid=False
    elif op=='CC':
     ks=[k for k in range(1,min(3,len(ones))+1)if ones[-k]==goal[0]]
     if not ks:valid=False
     opts[n]=ks
    return
   lo,hi=bounds(n)
   visit(n[0],zs+(hi,),ones)
   visit(n[1],zs,ones+(lo,))
  visit(sh)
  if not valid:continue
  for vals in itertools.product(*opts.values()):
   mm=dict(zip(opts,vals))
   def make(n):
    if isinstance(n,int):return ('CC',mm[n])if n in mm else word[n]
    return make(n[0]),make(n[1])
   nn=make(sh)
   assert s.boundary(nn)==(0,0,False)
   gg=s.graph_arithmetic(s.sites((nn,('CH',None))))[0]
   assert [x[1]for x in gg][:-1]==[x[1]for x in target]
   out.append(nn)
 return list(dict.fromkeys(out))


def dag(n):
 out=set()
 def go(n):
  if n in out:return
  out.add(n)
  if not s.leaf(n):go(n[0]);go(n[1])
 go(n);return out


def main():
 uv=assoc_cfg(p.loop2,{6:7,7:6})
 pv=assoc_cfg(p.pair,{6:1,1:6})
 # Two adjacent increments of distinct registers commute in the initial pair loop.
 pp=[]
 for n in pv:
  rr=s.sites(n); rr[1][1:],rr[2][1:]=rr[2][1:],rr[1][1:]
  pp.append(s.tree(rr))
 pv+=pp
 print('variants',len(uv),len(pv),flush=True)
 allresults=[];best=999
 for i,u in enumerate(uv):
  def remapinput(n):
   if s.leaf(n):return('CD',8)if n==('CD',2)else n
   return remapinput(n[0]),remapinput(n[1])
  u8=remapinput(u)
  for j,v in enumerate(pv):
   ch={p.loop2:u,p.loop8:u8,p.pair:v};c={'8':0,'10':0}
   tt=p.transform(q.TREE,ch,c)
   nn=len(dag(tt))
   rec={'unpair_variant':i,'pair_variant':j,'dag_nodes':nn}
   allresults.append(rec)
   if nn<=best:
    best=min(nn,best); print('cost',rec,flush=True)
   if nn<=208:
    d=OUT/f'u{i}_p{j}';d.mkdir(exist_ok=True);rr=s.sites(tt)
    rec['source_metrics']=s.metrics(tt)
    (d/'sites.json').write_bytes(s.compact(rr))
    try:
     U,m=z.compile_tree(q.T,q.TREE,tt);rec['compiler']=m;(d/'candidate.tm').write_bytes(b.table_bytes(U))
    except Exception as exc:rec['error']=repr(exc)
    (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 print('best',best,flush=True)
 (OUT/'summary.json').write_text(json.dumps({'unpair_variants':len(uv),'pair_variants':len(pv),'minimum_dag':best,'results':allresults},indent=2)+'\n')

if __name__=='__main__':main()
