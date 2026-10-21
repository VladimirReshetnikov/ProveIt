#!/usr/bin/env python3
"""Positive-block checker for a removed state's complemented entry marker.

The original all-initial-tape invariant is recomputed by check_joint_fold.
This checker compares represented whole configurations, not just control states.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json
import check_joint_fold as base

def verify(O,N,os,ns,keep,drop,tag,radius,fuel):
 Q={q for q,b in O};R={q for q,b in N}
 base.need(R==Q-{drop} and keep in R and drop!=os,'state map / initial relation')
 base.need(os==ns and tag in(-1,1),'initial state / marker offset')
 phi=lambda q:keep if q==drop else q
 I=base.domain(O,os,radius);hist=Counter();nontrivial=0;contexts=0
 def advance(table,q,h,m):
  b=(m>>(h+radius))&1;w,d,z=table[q,b]
  return z,h+d,(m&~(1<<(h+radius)))|(w<<(h+radius))
 def represent(q,h,m):
  if q==drop:
   if not -radius<=h+tag<=radius:return None
   return keep,h,m^(1<<(h+tag+radius))
  return q,h,m
 for q in sorted(Q):
  for b in(0,1):
   w,d,z=O[q,b]
   structural=(q!=drop and N[q,b]==(w^(z==drop),d,phi(z)) and(z!=drop or tag==-d))
   for m in sorted(I[q]):
    if((m>>radius)&1)!=b:continue
    contexts+=1
    if structural:hist[1,1]+=1;continue
    nontrivial+=1;old_goals={};old_halt=None;oq,oh,om=q,0,m
    for a in range(1,fuel+1):
     if oq==254 or not -radius<=oh<=radius:break
     oq,oh,om=advance(O,oq,oh,om)
     if oq==254:old_halt=a
     represented=represent(oq,oh,om)
     if represented is not None:old_goals.setdefault(represented,a)
    nq,nh,nm=represent(q,0,m)
    for bsteps in range(1,fuel+1):
     base.need(nq!=254 and -radius<=nh<=radius,f'new exits before join: {q},{m}')
     nq,nh,nm=advance(N,nq,nh,nm)
     if nq==254:
      base.need(old_halt is not None,f'new halt without old halt: {q},{m}')
      hist[old_halt,bsteps]+=1;break
     target=(nq,nh,nm)
     if target in old_goals:hist[old_goals[target],bsteps]+=1;break
    else:raise ValueError(f'no represented common endpoint: {q},{m}')
 base.need(sum(hist.values())==contexts,'context census')
 return {'status':'ALL_INITIAL_TAPE_MARKER_RELATION_PASS','old_states':len(Q),'new_states':len(R),'keep':keep,'drop':drop,'tag_offset':tag,'radius':radius,'fuel':fuel,'contexts':contexts,'nontrivial_contexts':nontrivial,'positive_block_histogram':[[a,b,n]for(a,b),n in sorted(hist.items())],'maximum_old_block':max(a for a,b in hist),'maximum_new_block':max(b for a,b in hist),'scope':'The removed state is represented by the keeper with the head unchanged and the bit at the fixed tag offset complemented. All other states use the identity tape relation. The initial relation is the identity. Every checked block is positive; no read outside the universally quantified window is allowed before a join. This is a relative halting theorem, not a theory-to-machine calibration.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--old',type=Path,required=True);ap.add_argument('--new',type=Path,required=True);ap.add_argument('--keep',type=int,required=True);ap.add_argument('--drop',type=int,required=True);ap.add_argument('--tag',type=int,default=-1);ap.add_argument('--radius',type=int,default=7);ap.add_argument('--fuel',type=int,default=97);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 O,os=base.read(a.old);N,ns=base.read(a.new);report=verify(O,N,os,ns,a.keep,a.drop,a.tag,a.radius,a.fuel)
 bad=N.copy();bad[ns,0]=(0,1,254)
 try:verify(O,bad,os,ns,a.keep,a.drop,a.tag,a.radius,a.fuel)
 except ValueError as exc:report['initial_halt_negative_control']={'status':'REJECTED','reason':str(exc)}
 else:raise ValueError('initial halt corruption accepted')
 sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 report.update(old_sha256=sha(a.old),new_sha256=sha(a.new),checker_sha256=sha(Path(__file__)),invariant_provider_sha256=sha(Path(base.__file__)))
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
