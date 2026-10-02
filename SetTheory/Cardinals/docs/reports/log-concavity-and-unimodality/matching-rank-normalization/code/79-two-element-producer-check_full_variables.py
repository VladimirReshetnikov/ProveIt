#!/usr/bin/env python3
"""Exact corroboration for a proposed ordinary multivariate matroid theorem."""
if not __debug__:raise SystemExit('Run without -O: assertions are required.')
import argparse,itertools,json,math,pathlib,random,time
from fractions import Fraction
from collections import defaultdict
import sympy as s

def symbolic():
 a,b,z,u,U0,UA,UB,UU,V,L0,L1,H,S=s.symbols('a b z u U0 UA UB UU V L0 L1 H S')
 R0=L0+H;R1=L1+H;M=L0*L1+H*(L0+L1)+S;Mx=L0*L1+H*(L0+L1)+H*H/2;W=L1*UA+L0*UB+H*UU
 f=z*z*U0+z*(a*R0+b*R1)*U0+a*b*M*U0+z*z*(a*UA+b*UB)+a*b*z*W+a*b*z*z*V
 def seed(x,y,w):return U0+x*UA+y*UB+w*UU+(x*y+x*w+y*w+w*w/2)*V
 expected=[(s.diff(f,z,2),2*seed(a,b,0)),(s.diff(f,a,b),M*seed(L1*z/M,L0*z/M,H*z/M)-(Mx-M)/M*z*z*V),(s.diff(f,a,z),R0*seed(2*z/R0+L1*b/R0,L0*b/R0,H*b/R0)-Mx/R0*b*b*V),(s.diff(f,b,z),R1*seed(L1*a/R1,2*z/R1+L0*a/R1,H*a/R1)-Mx/R1*a*a*V)]
 for left,right in expected:assert s.cancel(left-right)==0
 assert s.expand(s.hessian(z*z+(a*R0+b*R1)*z+a*b*M,(a,b,z)).det()-2*M*(R0*R1-M))==0
 for alpha,beta in itertools.product((0,1),repeat=2):
  ww=L1*alpha+L0*beta+H*max(alpha,beta)
  assert s.expand(R0*ww-alpha*M-alpha*(H*H-S)-(1-alpha)*beta*R0**2-alpha*beta*R0*L0)==0
  q=f.subs({U0:u,UA:alpha,UB:beta,UU:max(alpha,beta),V:0})
  hz=s.hessian(s.diff(q,z),(u,z,a,b));A=hz[:2,:2];B=hz[:2,2:]
  target=s.Matrix([[-2*R0*alpha,-H*alpha*beta],[-H*alpha*beta,-2*R1*beta]])
  assert (hz[2:,2:]-B.T*A.inv()*B-target).applyfunc(s.expand)==s.zeros(2)
 return {'rank_two_substitution_identities':4,'rank_zero_determinant':True,'rank_one_indicator_cases':4,'rank_one_schur_cases':4}

def combinations(n,k):return itertools.combinations(range(n),k) if 0<=k<=n else []
def old_polys(cols,A,B,q):
 n=len(cols)
 def basis(I,extra):
  vv=[cols[i] for i in I]+extra
  if len(vv)!=q:return False
  return q==0 or s.Matrix.hstack(*vv).det()!=0
 u0={I for I in combinations(n,q) if basis(I,[])}
 ua={I for I in combinations(n,q-1) if basis(I,[A])};ub={I for I in combinations(n,q-1) if basis(I,[B])}
 vv={I for I in combinations(n,q-2) if basis(I,[A,B])}
 return u0,ua,ub,ua|ub,vv

def polynomial(polys,n,L0,L1,common):
 U0,UA,UB,UU,V=polys;H=sum(common);S=sum(x*y for x,y in itertools.combinations(common,2));R0=L0+H;R1=L1+H;M=L0*L1+H*(L0+L1)+S
 f=defaultdict(int)
 def add(I,aa,bb,zz,c):
  if not c:return
  v=[int(i in I) for i in range(n)]+[aa,bb,zz];f[tuple(v)]+=c
 for I in U0:
  add(I,0,0,2,1);add(I,1,0,1,R0);add(I,0,1,1,R1);add(I,1,1,0,M)
 for I in UA:add(I,1,0,2,1);add(I,1,1,1,L1)
 for I in UB:add(I,0,1,2,1);add(I,1,1,1,L0)
 for I in UU:add(I,1,1,1,H)
 for I in V:add(I,1,1,2,1)
 return dict(f)

def positive_index(matrix):
 A=[[Fraction(x) for x in row] for row in matrix];pos=0
 while A:
  n=len(A);i=next((i for i in range(n) if A[i][i]),None)
  if i is not None:
   p=A[i][i];pos+=p>0
   if pos>1:return pos
   inds=[j for j in range(n) if j!=i]
   A=[[A[j][k]-A[j][i]*A[i][k]/p for k in inds] for j in inds]
  else:
   pair=next(((i,j) for i in range(n) for j in range(i+1,n) if A[i][j]),None)
   if pair is None:break
   i,j=pair;p=A[i][j];pos+=1
   if pos>1:return pos
   inds=[k for k in range(n) if k not in pair]
   A=[[A[k][l]-(A[k][i]*A[j][l]+A[k][j]*A[i][l])/p for l in inds] for k in inds]
 return pos

def check_poly(f,degree,exchange):
 n=len(next(iter(f)));quads={}
 for beta,c in f.items():
  assert sum(beta)==degree
  value=c*math.prod(math.factorial(x) for x in beta)
  for i in range(n):
   for j in range(i,n):
    if beta[i]<(2 if i==j else 1) or beta[j]<1:continue
    alpha=list(beta);alpha[i]-=1;alpha[j]-=1;alpha=tuple(alpha)
    mat=quads.setdefault(alpha,[[0]*n for _ in range(n)]);mat[i][j]+=value
    if i!=j:mat[j][i]+=value
 for alpha,mat in quads.items():assert positive_index(mat)<=1,(alpha,mat,f)
 checks=0
 if exchange:
  support=set(f)
  for aa in support:
   for bb in support:
    for i in range(n):
     if aa[i]<=bb[i]:continue
     good=False
     for j in range(n):
      if aa[j]>=bb[j]:continue
      x=list(aa);y=list(bb);x[i]-=1;x[j]+=1;y[i]+=1;y[j]-=1
      if tuple(x) in support and tuple(y) in support:good=True;break
     assert good,(aa,bb,i);checks+=1
 return len(quads),checks

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output-dir',type=pathlib.Path,default=pathlib.Path(__file__).parent);args=ap.parse_args();start=time.monotonic();sym=symbolic();rng=random.Random(239750);counts={'represented_matroid_cases':0,'exact_quadratic_inertia_checks':0,'M_convex_exchange_checks':0,'zero_population_parameter_cases':0};ranks={}
 for q,number in ((0,8),(1,16),(2,12),(3,12),(4,8),(5,4)):
  for case in range(number):
   cols=[s.eye(q)[:,i] for i in range(q)]+[s.Matrix([rng.randrange(-2,3) for _ in range(q)]) for _ in range(2)]
   zero=s.zeros(q,1)
   def random_col():return s.Matrix([rng.randrange(-2,3) for _ in range(q)])
   if q==1:A=s.Matrix([case%2]);B=s.Matrix([(case//2)%2])
   else:A=zero if case%4==0 else random_col();B=zero if case%4==1 else (A if case%4==2 else random_col())
   polys=old_polys(cols,A,B,q);L0=rng.randrange(5);L1=rng.randrange(5);common=[rng.randrange(4) for _ in range(rng.randrange(4))]
   f=polynomial(polys,len(cols),L0,L1,common);quad,ex=check_poly(f,q+2,q<=3)
   counts['represented_matroid_cases']+=1;counts['exact_quadratic_inertia_checks']+=quad;counts['M_convex_exchange_checks']+=ex;counts['zero_population_parameter_cases']+=L0==0 or L1==0 or sum(common)==0
   ranks[str(q)]=ranks.get(str(q),0)+1
 receipt={'status':'PASS','scope':'Exact corroboration of a proposed ordinary theorem, not a proof premise','symbolic':sym,'finite':counts,'rank_counts':ranks,'seconds':round(time.monotonic()-start,3)}
 args.output_dir.mkdir(parents=True,exist_ok=True);(args.output_dir/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
