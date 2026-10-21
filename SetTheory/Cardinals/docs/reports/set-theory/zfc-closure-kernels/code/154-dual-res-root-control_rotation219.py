#!/usr/bin/env python3
"""Reassociate source trees and recompute break/continue depths from exact CFG.

All accepted sources preserve every primitive effect and guarded ordinal edge.
Compiler results remain exploratory until full exact-table runtime validation.
"""
from pathlib import Path
from functools import cache
import sys,json,itertools,time,hashlib,collections,argparse,random
import os
HERE=Path(__file__).resolve().parent
ROOT=Path(os.environ.get('ROOT_RESEARCH_WORKSPACE', HERE/'generated')).resolve()
(ROOT/'root_work').mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(HERE.parent/'encoding'))
import encoding_support as q
import recompile219 as compiler
s,b=q.s,q.b
BASE=q.W/'K219_Construction_2026-10-20'
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
S=json.loads((BASE/'machine/sites219.json').read_text());old=s.tree(S)
G=s.graph_intervals(S);N=len(S)
assert s.graph_arithmetic(S)[0]==G
@cache
def nodes(t):
 return frozenset([t])if s.leaf(t)else nodes(t[0])|nodes(t[1])|{t}
@cache
def width(t):return 1 if s.leaf(t)else width(t[0])+width(t[1])
def replace_all(t,x,y):
 @cache
 def go(t):return y if t==x else t if s.leaf(t)else(go(t[0]),go(t[1]))
 return go(t)
def retarget(tree,mode=0):
 rows=s.sites(tree);intervals={};ix={r[0]:i for i,r in enumerate(rows)}
 def visit(n,p='',lo=0):
  hi=lo+width(n);intervals[p]=(lo,hi)
  if not s.leaf(n):visit(n[0],p+'0',lo);visit(n[1],p+'1',lo+width(n[0]))
 visit(tree)
 changes=[]
 for i,(p,op,arg)in enumerate(rows):
  assert [op,arg]==S[i][1:]or op in('CB','CC')and S[i][1]in('CB','CC')
  if op in('CI','CH'):continue
  def destinations(edge):
   ans=[]
   for j in range(len(p)-1,-1,-1):
    if p[j]==edge:ans.append(intervals[p[:j]][1]%N if edge=='0'else intervals[p[:j]][0])
   return ans
  if op=='CD':
   ds=destinations('0')
   if (ds[0]if ds else 0)!=G[i][1][0]:return None
   continue
  target=G[i][1][0];opts=[]
  for typ,edge,levels in [('CB','0',[1]),('CC','1',[1,2,3])]:
   ds=destinations(edge)
   for lev in levels:
    if(ds[lev-1]if len(ds)>=lev else 0)==target:opts.append((typ,lev))
  if not opts:return None
  choice=(op,arg)if(op,arg)in opts and mode!=2 else min(opts,key=lambda z:(z[0]!=op,z[1]))
  if mode==1 and len(opts)>1:choice=min(opts,key=lambda z:(z[1],z[0]))
  if mode==3 and len(opts)>1:choice=max(opts,key=lambda z:(z[1],z[0]))
  if choice!=(op,arg):rows[i][1:]=choice;changes.append([i,op,arg,*choice])
 new=s.tree(rows)
 assert s.graph_intervals(rows)==G
 assert s.graph_arithmetic(rows)[0]==G
 return new,changes
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--depth',type=int,default=1);ap.add_argument('--beam',type=int,default=30);ap.add_argument('--out',default='control_rotation219');args=ap.parse_args()
 out=ROOT/'root_work'/args.out;out.mkdir(exist_ok=True)
 seen={old};front=[(old,[])];results=[];start=time.time();hist=collections.Counter();total=0
 for depth in range(args.depth):
  nextfront=[]
  for tree,chain in front:
   for x in nodes(tree):
    if s.leaf(x):continue
    for direction in(0,1):
     if s.leaf(x[direction]):continue
     if direction==0:(a,bb),cc=x;y=(a,(bb,cc))
     else:a,(bb,cc)=x;y=((a,bb),cc)
     raw=replace_all(tree,x,y)
     for mode in(0,1):
      total+=1
      rr=retarget(raw,mode)
      if rr is None:hist['invalid_guard']+=1;continue
      new,changes=rr
      if new in seen:continue
      seen.add(new);m=s.metrics(new);hist[str(m['dag_nodes'])]+=1
      if m['maximum_zero_run']>6:hist['long_zero']+=1;continue
      ch=chain+[{'direction':direction,'subtree_sha':hashlib.sha256(s.compact(x)).hexdigest(),'depth_changes':changes}]
      if m['dag_nodes']<=207:
       rows=s.sites(new);key=hashlib.sha256(s.compact(rows)).hexdigest()[:16]
       rec={'key':key,'metrics':m,'chain':ch,'status':'EXACT_SOURCE_CFG; compiler/runtime separate'}
       try:U,cm=compiler.compile_tree(T,old,new);rec['compiler']=cm
       except Exception as exc:rec['error']=repr(exc);U=None
       if m['dag_nodes']<=206 or rec.get('compiler',{}).get('working_states',999)<=220:
        d=out/key;d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rows))
        if U is not None:(d/'candidate.tm').write_bytes(b.table_bytes(U))
        (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
        results.append(rec)
        print(json.dumps({k:rec[k]for k in('key','metrics','compiler','error')if k in rec}),flush=True)
       nextfront.append((m['dag_nodes'],rec.get('compiler',{}).get('working_states',999),new,ch))
  nextfront.sort(key=lambda t:(t[0],t[1]));front=[(n,ch)for _,_,n,ch in nextfront[:args.beam]]
  print('DEPTH',depth+1,'TOTAL',total,'UNIQUE',len(seen),'HIST',dict(hist),'SEC',round(time.time()-start,1),flush=True)
  (out/'summary.json').write_text(json.dumps({'depth':depth+1,'tested':total,'unique':len(seen),'histogram':dict(hist),'seconds':time.time()-start,'records':results},indent=2)+'\n')
if __name__=='__main__':main()
