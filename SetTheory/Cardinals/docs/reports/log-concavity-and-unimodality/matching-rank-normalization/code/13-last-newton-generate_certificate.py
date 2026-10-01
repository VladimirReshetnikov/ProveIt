#!/usr/bin/env python3
"""Exact generic-right profiles and diagnostic binomial-square certificates."""
from itertools import combinations_with_replacement
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import json
import sympy as s
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
from scipy.linalg import qr

PROFILES=[(1,2,4),(1,3,4),(3,3,4),(4,3,3),(4,7,3),(3,7,3),(7,7,3),(3,5,7),(3,7,7),(7,7,7)]
V=s.symbols('x1 x2 x4 y3 z3 y5 z5 y6 z6 y7 z7')
pairs=[None]*8;one={1:V[0],2:V[1],4:V[2]}
two={i:s.Integer(0) for i in range(1,8)};three=two.copy()
for i,j in [(3,3),(5,5),(6,7),(7,9)]:
 y,z=V[j:j+2];one[i]=y+z;two[i]=y*z+z*z/2
three[7]=V[9]*V[10]**2/2+V[10]**3/6
def match(masks):
 states={0}
 for mask in masks:
  new=set()
  for used in states:
   for i in range(3):
    if mask>>i&1 and not used>>i&1:new.add(used|(1<<i))
  states=new
 return bool(states)
def wt(I):
 out=s.Integer(1)
 for i in set(I):out*={1:one,2:two,3:three}[I.count(i)][i]
 return out
a=sum(sum(match([*I,1<<i]) for i in range(3))*wt(I) for I in combinations_with_replacement(range(1,8),2))
T=sum(int(match(I))*wt(I) for I in combinations_with_replacement(range(1,8),3))
a=s.expand(a);T=s.expand(T)
quad=[]
for i,j in combinations_with_replacement(range(len(V)),2):
 e=[0]*len(V);e[i]+=1;e[j]+=1;quad.append(tuple(e))
ratios=[Q(1,4),Q(1,3),Q(1,2),Q(2,3),Q(1),Q(3,2),Q(2),Q(3),Q(4)]
def addexp(x,y):return tuple(a+b for a,b in zip(x,y))
def endpoints(e):
 out=[]
 def walk(i,left,acc):
  if i==len(e):
   if left==0:out.append(tuple(acc))
   return
  for j in range(min(2*e[i],left)+1):walk(i+1,left-j,acc+[j])
 walk(0,4,[])
 return out
def cert(poly):
 terms={tuple(e):Q(c) for e,c in s.Poly(poly,*V).terms()}
 negative=[e for e,c in terms.items() if c<0]
 columns=[]
 for e in negative:
  for b in endpoints(e):
   c=tuple(2*x-y for x,y in zip(e,b))
   if b>=c:continue
   for r in ratios:
    d={e:Q(-1)}
    for key,val in [(b,r/2),(c,1/(2*r))]:d[key]=d.get(key,0)+val
    columns.append((b,c,r,d))
 universe=sorted(set(terms)|{e for *_,d in columns for e in d})
 index={e:i for i,e in enumerate(universe)}
 A=lil_matrix((len(universe),len(columns)),dtype=float)
 for j,(*_,d) in enumerate(columns):
  for e,c in d.items():A[index[e],j]=float(c)
 b=np.array([float(terms.get(e,0)) for e in universe])
 result=linprog(np.ones(len(columns)),A_ub=A.tocsr(),b_ub=b,bounds=(0,None),method='highs')
 info={'terms':len(terms),'negative_terms':len(negative),'candidate_squares':len(columns),'lp_success':bool(result.success),'message':result.message}
 if not result.success:return info
 coeff=[Q(float(x)).limit_denominator(1000000) for x in result.x]
 trial=terms.copy()
 for z,(*_,d) in zip(coeff,columns):
  if z:
   for e,c in d.items():trial[e]=trial.get(e,0)-z*c
 if any(v<0 for v in trial.values()):
  chosen=[i for i,x in enumerate(result.x) if x>1e-8]
  tight=[i for i,x in enumerate(result.ineqlin.residual) if abs(x)<1e-7]
  block=A.tocsr()[tight,:][:,chosen].toarray()
  _,_,piv=qr(block.T,pivoting=True,mode='economic')
  rows=[tight[int(i)] for i in piv[:len(chosen)]]
  exactM=s.Matrix([[s.Rational(columns[j][3].get(universe[i],0).numerator,columns[j][3].get(universe[i],Q(0)).denominator) for j in chosen] for i in rows])
  exactb=s.Matrix([s.Rational(terms.get(universe[i],Q(0)).numerator,terms.get(universe[i],Q(0)).denominator) for i in rows])
  solved=exactM.inv()*exactb
  coeff=[Q(0)]*len(columns)
  for j,x in zip(chosen,solved):coeff[j]=Q(x)
  if min(coeff)<0:raise RuntimeError('negative exact LP variable')
 residual=terms.copy();squares=[]
 for z,(m,n,r,d) in zip(coeff,columns):
  if not z:continue
  for e,c in d.items():residual[e]=residual.get(e,0)-z*c
  mu=tuple(min(i,j) for i,j in zip(m,n))
  left=tuple((i-j)//2 for i,j in zip(m,mu))
  right=tuple((i-j)//2 for i,j in zip(n,mu))
  squares.append({'multiplier':mu,'m':left,'n':right,'ratio':str(r),'weight':str(z)})
 bad={e:c for e,c in residual.items() if c<0}
 info.update({'exact':not bad,'square_count':len(squares),'negative_residuals':len(bad)})
 if bad:info['bad_samples']=[(list(e),str(c)) for e,c in list(bad.items())[:5]]
 else:
  info['squares']=squares
  info['positive_remainder']=[{'exponent':e,'coefficient':str(c)} for e,c in residual.items() if c>0]
 return info
out=[]
for k,(S1,S2,N) in enumerate(PROFILES):
 P=sum(sum(match([*I,Sv]) for Sv in [S1,S2])*wt(I) for I in combinations_with_replacement(range(1,8),2))
 B=sum(sum(match([i,1<<j,Sv]) for j in range(3) for Sv in [S1,S2])*one[i] for i in range(1,8))
 beta=sum(one[i] for i in range(1,8) if i&N)
 f=s.expand(2*a*P-T*(2*B+beta))
 answer=cert(f);answer['profile']=[S1,S2,N];out.append(answer)
 print(json.dumps({k:v for k,v in answer.items() if k not in ['squares','positive_remainder']}),flush=True)
 Path(__file__).with_suffix('.json').write_text(json.dumps({'variables':[str(x) for x in V],'profiles':out},indent=2)+'\n')
