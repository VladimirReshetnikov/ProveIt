#!/usr/bin/env python3
"""Small deterministic closed-rotation beam; exact partial-selector subtree frozen.
No claim of optimality. Full word/dual CFG checked for every saved finalist.
"""
import argparse,json,time,sys,hashlib
from functools import cache
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent/'vendor'))
import source_language as s
import source_splice as sp

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--seconds',type=float,default=20);a=ap.parse_args();a.output.mkdir(exist_ok=False)
 original=s.tree(json.loads(a.source.read_text()));baseline=s.tree(json.loads(a.baseline.read_text()));frozen=sp.serial(sp.closed_forest(baseline,398,4572))
 nodes=[];lookup={}
 def intern(x):
  if x not in lookup:lookup[x]=len(nodes);nodes.append(x)
  return lookup[x]
 def encode(t):return intern(t if s.leaf(t) else (encode(t[0]),encode(t[1])))
 def leaf(n):return isinstance(nodes[n][0],str)
 @cache
 def decode(n):return nodes[n] if leaf(n) else tuple(decode(x) for x in nodes[n])
 @cache
 def closed(n):return s.boundary(decode(n))==(0,0,False)
 def reach(root):
  out=set();todo=[root]
  for n in todo:
   if n in out:continue
   out.add(n)
   if not leaf(n):todo.extend(nodes[n])
  return out
 protected=reach(encode(frozen));base=encode(original);assert encode(frozen) in reach(base)
 @cache
 def shape(n):
  if leaf(n):return 0,0,0
  l,r=nodes[n];ld,lz,ll=shape(l);rd,rz,rl=shape(r)
  return max(ld,rd)+1,max(lz,rz,ll+1),ll+1
 def replace(root,old,new):
  memo={}
  def go(n):
   if n==old:return new
   if leaf(n):return n
   if n not in memo:memo[n]=intern(tuple(go(x) for x in nodes[n]))
   return memo[n]
  return go(root)
 def moves(root):
  for n in sorted(reach(root)-protected):
   if leaf(n):continue
   l,r=nodes[n]
   if not leaf(r):
    m,z=nodes[r]
    if all(closed(x) for x in (l,m,z)):yield n,intern((intern((l,m)),z)),'left'
   if not leaf(l):
    x,m=nodes[l]
    if all(closed(y) for y in (x,m,r)):yield n,intern((x,intern((m,r)))),'right'
 def score(n):
  depth,zero,_=shape(n);return len(reach(n)),zero,depth,n
 started=time.monotonic();beam=[base];seen={base};parents={};kept={base};rounds=0;expanded=0;complete=True
 for step in range(20):
  nexts=set(beam)
  for root in beam:
   for old,new,direction in moves(root):
    if time.monotonic()-started>a.seconds:complete=False;break
    rr=replace(root,old,new)
    if rr in seen:continue
    seen.add(rr);expanded+=1;depth,zero,_=shape(rr)
    if zero<=6 and depth<=64:
     nexts.add(rr);parents[rr]=(root,old,new,direction);kept.add(rr)
   if not complete:break
  rounds=step+1;newbeam=sorted(nexts,key=score)[:24]
  if not complete or newbeam==beam:break
  beam=newbeam
 ordered=sorted(kept,key=score);best=score(ordered[0])[0]
 finalists=[r for r in ordered if score(r)[0]==best][:16];summaries=[]
 origrows=s.sites(original);origg=sp.cfg_intervals(origrows);assert origg==sp.cfg_arithmetic(origrows)
 for i,n in enumerate(finalists):
  tree=decode(n);rows=s.sites(tree);assert [x[1:]for x in rows]==[x[1:]for x in origrows]
  assert sp.cfg_intervals(rows)==sp.cfg_arithmetic(rows)==origg and s.graph_intervals(rows)==s.graph_arithmetic(rows)[0]
  assert encode(frozen) in reach(n)
  raw=s.compact(rows);name=f'candidate{i:02d}.json';(a.output/name).write_bytes(raw)
  chain=[];cur=n
  while cur!=base:
   par,old,new,direction=parents[cur];chain.append({'old_tree':decode(old),'new_tree':decode(new),'direction':direction});cur=par
  summaries.append({'source':name,'sha256':hashlib.sha256(raw).hexdigest(),'metrics':s.metrics(tree),'rotations':list(reversed(chain)),'full_word_and_dual_CFG':True})
 result={'status':'BOUNDED_CLOSED_ROTATION_BEAM_COMPLETE' if complete else 'BOUNDED_CLOSED_ROTATION_BEAM_TIME_CAP','input':str(a.source),'input_sha256':hashlib.sha256(a.source.read_bytes()).hexdigest(),'beam':24,'maximum_rounds':20,'rounds':rounds,'seen':len(seen),'expanded':expanded,'seconds':time.monotonic()-started,'frozen_original_span':[398,4572],'frozen_subtree_unchanged':True,'minimum_saved_DAG':best,'finalists':summaries,'scope':'Bounded beam only, not an exhaustive source/grammar minimum; no allocator or machine execution.'}
 (a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='finalists'},indent=2))
if __name__=='__main__':main()
