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
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--seconds',type=float,default=20);ap.add_argument('--beam',type=int,default=128);ap.add_argument('--rounds',type=int,default=100);a=ap.parse_args();a.output.mkdir(exist_ok=False)
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
 protected=set();base=encode(original);assert encode(frozen) in reach(base)
 @cache
 def size(n):return 1 if leaf(n) else sum(size(x) for x in nodes[n])
 def critical(root):
  found=set()
  def visit(n,i):
   j=i+size(n)
   if j<=398 or i>=4572:return
   if (i,j) in ((398,4572),(398,4560),(4560,4572)):found.add(n)
   if not leaf(n):
    visit(nodes[n][0],i);visit(nodes[n][1],i+size(nodes[n][0]))
  visit(root,0)
  assert len(found)==3
  return found
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
  for n in sorted(reach(root)-protected-critical(root)):
   if leaf(n):continue
   l,r=nodes[n]
   if not leaf(r):
    m,z=nodes[r]
    if s.boundary(decode(l))[0]==0 and s.boundary(decode(z))[1]==0:yield n,intern((intern((l,m)),z)),'left'
   if not leaf(l):
    x,m=nodes[l]
    if s.boundary(decode(x))[0]==0 and s.boundary(decode(r))[1]==0:yield n,intern((x,intern((m,r)))),'right'
 def score(n):
  depth,zero,_=shape(n);return len(reach(n))+2*zero,len(reach(n)),zero,depth,n
 started=time.monotonic();beam=[base];seen={base};parents={};kept={base};rounds=0;expanded=0;complete=True
 for step in range(a.rounds):
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
  rounds=step+1;newbeam=sorted(nexts,key=score)[:a.beam]
  if not complete or newbeam==beam:break
  beam=newbeam
 ordered=sorted(kept,key=score);best=score(ordered[0])[0]
 finalists=[r for r in ordered if score(r)[0]==best][:16];summaries=[]
 origrows=s.sites(original);origg=sp.cfg_intervals(origrows);assert origg==sp.cfg_arithmetic(origrows)
 for i,n in enumerate(finalists):
  tree=decode(n);rows=s.sites(tree);assert [x[1:]for x in rows]==[x[1:]for x in origrows]
  assert sp.cfg_intervals(rows)==sp.cfg_arithmetic(rows)==origg and s.graph_intervals(rows)==s.graph_arithmetic(rows)[0]
  critical(n)
  raw=s.compact(rows);name=f'candidate{i:02d}.json';(a.output/name).write_bytes(raw)
  chain=[];cur=n
  while cur!=base:
   par,old,new,direction=parents[cur];chain.append({'old_tree':decode(old),'new_tree':decode(new),'direction':direction});cur=par
  summaries.append({'source':name,'sha256':hashlib.sha256(raw).hexdigest(),'metrics':s.metrics(tree),'rotations':list(reversed(chain)),'full_word_and_dual_CFG':True})
 result={'status':'BOUNDED_CLOSED_ROTATION_BEAM_COMPLETE' if complete else 'BOUNDED_CLOSED_ROTATION_BEAM_TIME_CAP','input':str(a.source),'input_sha256':hashlib.sha256(a.source.read_bytes()).hexdigest(),'beam':a.beam,'maximum_rounds':a.rounds,'rounds':rounds,'seen':len(seen),'expanded':expanded,'seconds':time.monotonic()-started,'frozen_subtrees':[],'selector_frame_intervals':[[398,4572],[398,4560],[4560,4572]],'best_DAG_plus_two_zero_runs':best,'finalists':summaries,'scope':'Bounded beam only, not an exhaustive source/grammar minimum; no allocator or machine execution.'}
 (a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='finalists'},indent=2))
if __name__=='__main__':main()
