#!/usr/bin/env python3
"""Exact reproducibility checker for weighted rank-four support theorem.
Python >=3.10 and SymPy. No floating-point arithmetic or numerical-root claims.
Run beside support_kernels.py.
"""
import json,itertools
from fractions import Fraction as F
from itertools import combinations
from random import Random
import sympy as s
from support_kernels import perfectly_matchable,minimum_bipartite_cover,quota_vectors

def terms(core):
 out=[[] for _ in range(5)]
 qs=list(quota_vectors([2]*3,2))
 for lm,rm,lq,rq in itertools.product(range(4),range(4),qs,qs):
  ls=[i for i in range(2) if lm>>i&1];rs=[j for j in range(2) if rm>>j&1]
  le=[t for t,q in enumerate(lq,1) for _ in range(q)];re=[t for t,q in enumerate(rq,1) for _ in range(q)]
  k=len(ls)+len(le)
  if k!=len(rs)+len(re):continue
  rows=[]
  for i in ls:
   rows.append(sum(1<<j for j,o in enumerate(rs) if core>>(i*2+o)&1)+sum(1<<(len(rs)+j) for j,t in enumerate(re) if t>>i&1))
  rows += [sum(1<<j for j,o in enumerate(rs) if t>>o&1) for t in le]
  if not perfectly_matchable(tuple(rows)):continue
  if lq[0]>1 or lq[1]>1 or rq[0]>1 or rq[1]>1:continue
  ids=ls+[2+j for j in rs]
  for q,base in ((lq,4),(rq,8)):
   ids += [base+i for i in range(3) if q[i]==1]
   if q[2]==2:ids.append(base+3)
  out[k].append(ids)
 return out


def prod(vals):
 out=F(1)
 for x in vals:out*=x
 return out

def convolution(a,b):
 out=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out

def core_formula(core,V):
 al=V[:2];be=V[2:4];L=V[4:7];R=V[8:11]
 qL=[1,be[0]*(L[0]+L[2])+be[1]*(L[1]+L[2]),prod(be)*(L[0]*L[1]+L[2]*(L[0]+L[1])+V[7])]
 qR=[1,al[0]*(R[0]+R[2])+al[1]*(R[1]+R[2]),prod(al)*(R[0]*R[1]+R[2]*(R[0]+R[1])+V[11])]
 P=convolution(qL,qR)
 edges=[(i,j) for i in range(2) for j in range(2) if core>>(2*i+j)&1]
 P[1]+=sum(al[i]*be[j] for i,j in edges)
 # Imbalance one: one exterior vertex on exactly one side.
 for i in range(2):
  eligible=sum(L[t-1] for t in (1,2,3) if any(ii==i and t>>(1-j)&1 for ii,j in edges))
  P[2]+=al[i]*prod(be)*eligible
 for j in range(2):
  eligible=sum(R[t-1] for t in (1,2,3) if any(jj==j and t>>(1-i)&1 for i,jj in edges))
  P[2]+=be[j]*prod(al)*eligible
 # Imbalance two: the four core vertices, counted once.
 if ((0,0) in edges and (1,1) in edges) or ((0,1) in edges and (1,0) in edges):P[2]+=prod(al+be)
 # Imbalance one: one exterior vertex on each side; Boolean OR over core edges.
 P[3]+=prod(al+be)*sum(L[t-1]*R[w-1] for t in (1,2,3) for w in (1,2,3) if any(t>>(1-j)&1 and w>>(1-i)&1 for i,j in edges))
 return P

def exact_graph_checks():
 rng=Random(431);count=0
 for core in range(16):
  for repetition in range(8):
   nl,nr=rng.randrange(1,4),rng.randrange(1,4)
   V=[F(rng.randrange(1,10),rng.randrange(1,6)) for _ in range(12)]
   lc=[F(rng.randrange(1,10),rng.randrange(1,6)) for _ in range(nl)]
   rc=[F(rng.randrange(1,10),rng.randrange(1,6)) for _ in range(nr)]
   V[6]=sum(lc,F(0));V[7]=sum((x*y for x,y in combinations(lc,2)),F(0))
   V[10]=sum(rc,F(0));V[11]=sum((x*y for x,y in combinations(rc,2)),F(0))
   lw=V[:2]+[V[4],V[5]]+lc;rw=V[2:4]+[V[8],V[9]]+rc
   rows=[sum(1<<j for j in range(2) if core>>(i*2+j)&1)+sum(1<<(2+j) for j,t in enumerate([1,2]+[3]*nr) if t>>i&1) for i in range(2)]
   rows += [1,2]+[3]*nl
   assert sum(map(len,minimum_bipartite_cover(rows,len(rw))))==4
   actual=[F(0)]*5
   for k in range(5):
    for ii in combinations(range(len(lw)),k):
     for jj in combinations(range(len(rw)),k):
      rr=tuple(sum(1<<j for j,v in enumerate(jj) if rows[i]>>v&1) for i in ii)
      if perfectly_matchable(rr):actual[k]+=prod([lw[i] for i in ii]+[rw[j] for j in jj])
   kernel=[sum((prod([V[i] for i in ids]) for ids in tt),F(0)) for tt in terms(core)]
   formula=core_formula(core,V)
   assert actual==kernel==formula,(core,repetition,actual,kernel,formula)
   assert all(k*(4-k)*actual[k]**2>=(k+1)*(5-k)*actual[k-1]*actual[k+1] for k in (1,2,3))
   count+=1
 return count

def pair_neighborhood_checks():
 for n in range(1,7):
  types=[3]*n+[5]*n+[6]*n
  rows=[sum(1<<j for j,typ in enumerate(types) if typ>>i&1) for i in range(3)]
  actual=[]
  for k in range(4):
   count=0
   for ii in combinations(range(3),k):
    for jj in combinations(range(3*n),k):
     rr=tuple(sum(1<<h for h,j in enumerate(jj) if rows[i]>>j&1) for i in ii)
     count+=perfectly_matchable(rr)
   actual.append(count)
  assert actual==[1,6*n,3*n*(7*n-1)//2,4*n**3-3*n**2],(n,actual)
 return 6

def symbolic_checks():
 X,Y,Z,E,u,v=s.symbols('X Y Z E u v',real=True);U=u+v;a=u*v
 A=u*(X+Z)+v*(Y+Z);B=a*(X*Y+X*Z+Y*Z+E);alpha=a*(X+Y+Z)/U
 D=alpha*(A-alpha)-B;delta=A*A-4*B
 assert s.factor(2*U*U*D-a*delta-a*((u*X-v*Y)**2+(u*u+v*v)*(Z*Z-2*E)))==0
 theta=u/U;T=theta*X-(1-theta)*Y+(theta-s.Rational(1,2))*Z
 assert s.factor(D-a*(T*T+3*Z*Z/4-E))==0
 # Exact block identity in diagonal eigenbases, with one arbitrary complex phase entry.
 e,f,g,h,r,q,w,x,y,t=s.symbols('e f g h r q w x y t',real=True)
 C=s.Matrix([[r,q],[w,x+s.I*y]]);GA=s.diag(e*e,f*f);GB=s.diag(g*g,h*h)
 M=C.row_join(s.diag(e,f)).col_join(s.diag(g,h).row_join(s.zeros(2)))
 H=s.eye(4)+t*M*M.conjugate().T
 lhs=s.expand(sum((-1)**sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4))*s.prod(H[i,perm[i]] for i in range(4)) for perm in itertools.permutations(range(4))))
 HA=GA.adjugate();HB=GB.adjugate();Cs=C.conjugate().T
 rhs=(1+s.trace(GA)*t+GA.det()*t*t)*(1+s.trace(GB)*t+GB.det()*t*t)+t*s.trace(C*Cs)+t*t*(s.trace(HA*C*Cs)+s.trace(C*HB*Cs)+C.det()*s.conjugate(C.det()))+t**3*s.trace(HA*C*HB*Cs)
 assert s.expand(lhs-rhs)==0
 assert s.discriminant(1+9*t+24*t*t+16*t**3+t**4,t)==-5243
 n=s.symbols('n')
 pn=1+6*n*t+3*n*(7*n-1)*t*t/2+(4*n**3-3*n*n)*t**3
 assert s.factor(s.discriminant(pn,t)+s.Rational(27,2)*n**3*(n**3-3*n*n-3*n-1))==0
 assert s.discriminant(pn.subs(n,4),t)==-2592
 return ['weighted variance identity','weighted adjacent-core interlacing identity','full-core complex PSD block coefficient identity','theta quartic discriminant = -5243','pair-neighborhood cubic discriminant formula and n=4 value -2592']

if __name__=='__main__':
 count=exact_graph_checks();pair_count=pair_neighborhood_checks();checks=symbolic_checks()
 receipt={'status':'PASS','exact_labeled_graphs':count,'pair_neighborhood_graphs':pair_count,'pair_neighborhood_populations':list(range(1,7)),'core_masks':list(range(16)),'comparisons':['labeled-support enumeration','Boolean cover-type kernel','independent shore-imbalance coefficient formula'],'matching_rank_verified':4,'activities':'nonuniform positive rational vertex activities; common-type populations 1 through 3','seed':431,'sympy_version':s.__version__,'symbolic_checks':checks,'scope':'Finite checks supplement the written proof; they do not establish universal positivity by enumeration.'}
 print(json.dumps(receipt,indent=2))
