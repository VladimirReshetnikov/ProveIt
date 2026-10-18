#!/usr/bin/env python3
"""Exact affine-relation analysis with nonnegative cancellation and finite masks.

The abstract value is an affine subspace of Q^9 represented as the row span
of lifted points (1,x_0,...,x_8). Natural-valued source configurations lie
in that subspace. Joins are affine hulls; all calculations use Fraction.
This is source analysis only and supplies no modified binary proof.
"""
from fractions import Fraction as F
from pathlib import Path
from collections import deque,Counter
import json,time,sys
import mp_dirty_phase as ctx

HERE=Path(__file__).resolve().parent
DIM=10

def pivot(row):
 return next((i for i,x in enumerate(row) if x),DIM)

def add_vector(basis, vector):
 v=list(vector)
 for row in basis:
  p=pivot(row);a=v[p]
  if a:
   for j in range(p,DIM):
    if row[j]:v[j]-=a*row[j]
 p=pivot(v)
 if p==DIM:return basis
 a=v[p]
 if a!=1:
  for j in range(p,DIM):
   if v[j]:v[j]=F(v[j],a)
 v=tuple(v);out=[]
 for row in basis:
  a=row[p]
  if a:
   r=list(row)
   for j in range(p,DIM):
    if v[j]:r[j]-=a*v[j]
   out.append(tuple(r))
  else:out.append(row)
 out.append(v);out.sort(key=pivot)
 return tuple(out)

def hull(a,b):
 out=a
 for row in b:out=add_vector(out,row)
 return out

def meet_coordinate(basis, register, value):
 if basis is None:return None
 col=register+1
 vals=[r[col]-value*r[0] for r in basis]
 if not any(vals):return basis
 # An affine point exists exactly when this equation can be satisfied by
 # a direction, or is already satisfied by the fixed affine point.
 index=next((i for i in range(1,len(vals)) if vals[i]),None)
 if index is None:return None
 v=basis[index];scale=vals[index];out=()
 for i,row in enumerate(basis):
  if i==index:continue
  ratio=F(vals[i],scale)
  new=tuple(a-ratio*b if b and ratio else a for a,b in zip(row,v))
  out=add_vector(out,new)
 assert out and out[0][0]==1
 return out

def is_constant(basis,register):
 col=register+1
 return basis[0][col] if all(not r[col] for r in basis[1:]) else None

def refine(basis,masks):
 if basis is None or masks is None:return None
 for reg,mask in enumerate(masks):
  if mask in (1,2):
   basis=meet_coordinate(basis,reg,mask-1)
   if basis is None:return None
 for reg,mask in enumerate(masks):
  c=is_constant(basis,reg)
  if c is None:continue
  if c<0 or F(c).denominator!=1:return None
  tag=1 if c==0 else 2 if c==1 else 4
  if not mask&tag:return None
 # Nonnegative cancellation: a canonical equation
 # x_j + sum(c_i*x_i) = C with all c_i >= 0 bounds every term.
 # If the sum of mask lower bounds already equals C, every term
 # is forced to its lower bound. If that sum exceeds C, no natural
 # configuration satisfies this abstract state.
 while True:
  updated=False
  pivots=[pivot(r) for r in basis]
  for col in range(1,DIM):
   if col in pivots:continue
   if any(r[col]>0 for r in basis[1:]):continue
   terms=[(col-1,F(1))]+[(pivot(r)-1,-r[col]) for r in basis[1:] if r[col]<0]
   constant=basis[0][col]
   lower=lambda mask: 0 if mask&1 else 1 if mask&2 else 2
   bound=sum(weight*lower(masks[reg]) for reg,weight in terms)
   if bound>constant:return None
   if bound==constant:
    previous=basis
    for reg,weight in terms:
     basis=meet_coordinate(basis,reg,lower(masks[reg]))
     if basis is None:return None
    if previous!=basis:updated=True;break
  if not updated:break
 return basis

def shift(basis,register,delta):
 row=list(basis[0]);row[register+1]+=delta
 dirs=basis[1:]
 # Directions have first coordinate zero, so the affine point is the
 # only lifted basis row changed by x_register := x_register + delta.
 for direction in dirs:
  p=pivot(direction);a=row[p]
  if a:
   for j in range(p,DIM):
    if direction[j]:row[j]-=a*direction[j]
 return (tuple(row),)+dirs

def transfer(basis,case):
 if basis is None:return None
 site,pc,op,reg,zero=case
 if op=='CI':return shift(basis,reg,1)
 if op=='CD':
  if zero:return meet_coordinate(basis,reg,0)
  if is_constant(basis,reg)==0:return None
  return shift(basis,reg,-1)
 return basis

def subset(a,b):
 return hull(b,a)==b

def main():
 began=time.monotonic()
 points=[None]*len(ctx.sites)
 initial=(1,0,0,0,0,1,1,0,0,0)
 points[ctx.first]=(initial,)
 queue=deque([ctx.first]);pops=0;changes=0
 while queue:
  site=queue.popleft();pops+=1
  for i in ctx.by_site[site]:
   target=ctx.targets[i]
   if target is None:continue
   value=refine(transfer(points[site],ctx.cases[i]),ctx.values[target])
   if value is None:continue
   old=points[target]
   joined=value if old is None else hull(old,value)
   if old!=joined:
    points[target]=joined;queue.append(target);changes+=1
  if pops%10000==0:print('AFFINE pops',pops,'queue',len(queue),'seconds',time.monotonic()-began,flush=True)
 assert subset((initial,),points[ctx.first])
 enabled=[];obligations=0
 for i,(case,target) in enumerate(zip(ctx.cases,ctx.targets)):
  value=transfer(points[case[0]],case)
  if target is not None:value=refine(value,ctx.values[target])
  enabled.append(value is not None)
  if value is not None and target is not None:
   assert points[target] is not None and subset(value,points[target]),i
   obligations+=1
 excluded=[i for i,b in enumerate(enabled) if not b]
 result={'scope':__doc__,'initial_registers':list(initial[1:]),'sites':len(points),
         'guards':len(enabled),'pops':pops,'changes':changes,'postfix_obligations':obligations,
         'excluded':[dict(index=i,site=ctx.cases[i][0],path=ctx.cases[i][1],op=ctx.cases[i][2],register=ctx.cases[i][3],zero=ctx.cases[i][4]) for i in excluded],
         'lifted_dimension_counts':dict(Counter(len(p) if p is not None else 0 for p in points)),
         'elapsed_seconds':time.monotonic()-began}
 (HERE/'mp_affine_nonnegative.json').write_text(json.dumps(result,indent=2)+'\n')
 # Keep the complete exact post-fixpoint as a compressed, reviewable value.
 import gzip
 serial=[None if p is None else [[[F(x).numerator,F(x).denominator] for x in row] for row in p] for p in points]
 with gzip.open(HERE/'mp_affine_nonnegative_spaces.json.gz','wt') as f:json.dump(serial,f,separators=(',',':'))
 print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
