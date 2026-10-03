"""Independent exact endpoint checks for star-core gluing and core scaling.
No matchings are counted with multiplicity. Symbolic identities use SymPy.
"""
from verify_union_formula import coeffs,add,scale,shift,mul,difference,trim
from itertools import product
from random import Random
from pathlib import Path
import json
import sympy as S

def rooted(adj,u,v,side,index):
 uu=u[:];vv=v[:]
 (uu if side=='L' else vv)[index]=0
 A=coeffs(adj,uu,vv)
 (uu if side=='L' else vv)[index]=1
 p=coeffs(adj,uu,vv)
 dif=difference(p,A);assert dif[0]==0
 return A,trim(dif[1:] or [0])

def gaps(p,r):
 p=p+[0]*(r+1-len(p))
 return [k*(r-k)*p[k]**2-(k+1)*(r-k+1)*p[k-1]*p[k+1] for k in range(1,r)]

def star_trial(q,kind,mask,rng):
 L=[rng.randrange(1<<q) for _ in range(rng.randrange(5))]
 R=[rng.randrange(4) for _ in range(rng.randrange(5))]
 ul=[rng.randrange(1,8) for _ in L];vr=[rng.randrange(1,8) for _ in R]
 ua=[rng.randrange(1,8) for _ in range(2)];vb=[rng.randrange(1,8) for _ in range(q)]
 core=[mask,0] if kind=='row' else [int(mask&1),int(bool(mask&2))]
 H=[{j for j in range(q) if m>>j&1} for m in L]
 full=[{j for j in range(q) if core[i]>>j&1}|{q+j for j,m in enumerate(R) if m>>i&1} for i in range(2)]+H
 actual=coeffs(full,ua+ul,vb+vr)
 if kind=='row':
  a1=[{j for j in range(q) if mask>>j&1}]+H
  a2=[{j for j,m in enumerate(R) if m>>i&1} for i in range(2)]
  A,B=rooted(a1,[ua[0]]+ul,vb,'L',0)
  C,D=rooted(a2,ua,vr,'L',0)
  root=ua[0]
  assert len(C)<=2 and len(D)<=2
 else:
  a1=H
  a2=[({0} if mask>>i&1 else set())|{1+j for j,m in enumerate(R) if m>>i&1} for i in range(2)]
  A,B=rooted(a1,ul,vb,'R',0)
  C,D=rooted(a2,ua,[vb[0]]+vr,'R',0)
  root=vb[0]
  assert len(C)<=3 and len(D)<=2
 expected=add(mul(A,C),shift(scale(add(mul(B,C),mul(A,D)),root)))
 assert actual==expected,(q,kind,mask,L,R,actual,expected)
 assert min(gaps(actual,q+2),default=0)>=0
 return len(actual)-1==q+2

def weighted_core_table(adj,u,v,lc=2,rc=3):
 n=len(v);wp=[1]*(1<<n)
 for J in range(1,1<<n):
  b=J&-J;wp[J]=wp[J-b]*v[b.bit_length()-1]
 out=[[0]*6 for _ in range(6)]
 for I in range(1<<len(u)):
  k=I.bit_count()
  if k>5:continue
  reach={0};w=1
  for i in range(len(u)):
   if I>>i&1:
    w*=u[i];reach={J|(1<<j) for J in reach for j in adj[i] if not J>>j&1}
    if not reach:break
  for J in reach:
   core=(I&((1<<lc)-1)).bit_count()+(J&((1<<rc)-1)).bit_count()
   out[k][core]+=w*wp[J]
 return [trim(a) for a in out]

def scaling_trial(core,rng):
 # Private exterior vertices ensure rank five; extra vertices are unrestricted.
 L=[1,2,4]+[rng.randrange(8) for _ in range(3)]
 R=[1,2]+[rng.randrange(4) for _ in range(3)]
 u=[rng.randrange(1,10) for _ in range(2+len(L))]
 v=[rng.randrange(1,10) for _ in range(3+len(R))]
 H=[{j for j in range(3) if m>>j&1} for m in L]
 adj=[{j for j in range(3) if core[i]>>j&1}|{3+j for j,m in enumerate(R) if m>>i&1} for i in range(2)]+H
 a=weighted_core_table(adj,u,v)
 ep=coeffs([{j for j in range(3) if m>>j&1} for m in core],u[:2],v[:3])
 e1,e2=ep[1:3];g0,g1,g2=[a[k][5] for k in (3,4,5)]
 assert e1>0 and e2>0 and g0>0 and g2>0
 assert e1*e1>=4*e2 and g1*g1>=3*g0*g2
 limits=[4*e1*e1-10*e2,6*e2*e2,6*g0*g0,4*g1*g1-10*g0*g2]
 ds=[4,8,10,10];threshold=S.Rational(1)
 gg=[]
 for k,d,lead in zip(range(1,5),ds,limits):
  z=difference(scale(mul(a[k],a[k]),k*(5-k)),scale(mul(a[k-1],a[k+1]),(k+1)*(6-k)))
  assert len(z)==d+1 and z[d]==lead and lead>0
  threshold=max(threshold,1+S.Rational(sum(max(-b,0) for b in z[:-1]),lead));gg.append(z)
 w=int(S.ceiling(threshold))
 assert all(sum(b*w**i for i,b in enumerate(z))>0 for z in gg)
 return w

def symbolic():
 s,t,x,y,a,b,c,de=S.symbols('s t x y a b c de')
 c1=x*(a+c)+y*(b+c);c2=x*y*(a*b+a*c+b*c+de)
 assert S.expand(c1*c1-4*c2-(x*(a+c)-y*(b+c))**2-4*x*y*(c*c-de))==0
 for e,f,rhs in [(x,x*y*(b+c),x**3*y*(c*c-de)),(y,x*y*(a+c),x*y**3*(c*c-de)),(x+y,x*y*(a+b+c),x*y*((a*x-b*y+c*(x-y)/2)**2+(3*c*c/4-de)*(x+y)**2))]:
  assert S.expand(c1*e*f-f*f-c2*e*e-rhs)==0
 d,e,f=S.symbols('d e f');K=s*s+d*s*t+e*s*x+f*t*x
 assert S.expand(S.hessian(K,(s,t,x)).det()-2*f*(d*e-f))==0
 u=S.symbols('u')
 for q in range(1,6):
  aa=S.symbols('a0:'+str(q+1));bb=S.symbols('b0:'+str(q))
  Ah=sum(aa[i]*s**(q-i)*t**i for i in range(q+1));Bh=sum(bb[i]*s**(q-1-i)*t**i for i in range(q))
  prod=S.Poly(S.expand((Ah+x*Bh)*K),x)
  trunc=prod.nth(0)+x*prod.nth(1)
  want=Ah*(s*s+d*s*t)+u*t*(Bh*(s*s+d*s*t)+Ah*(e*s+f*t))
  assert S.expand(trunc.subs(x,u*t)-want)==0
  aa=S.symbols('c0:'+str(q));bb=S.symbols('d0:'+str(q))
  Ah=sum(aa[i]*s**(q-1-i)*t**i for i in range(q));Bh=sum(bb[i]*s**(q-1-i)*t**i for i in range(q))
  c1,c2=S.symbols('c1 c2');Ch=s*s+c1*s*t+c2*t*t;Dh=e*s+f*t;F=x*Ah+t*Bh
  got=u*(Ch*F+s*t*Dh*S.diff(F,x)).subs(x,s/u)
  assert S.expand(got-(s*Ah*Ch+u*t*Bh*Ch+u*s*t*Ah*Dh))==0

if __name__=='__main__':
 rng=Random(170522);stars=full=0
 for q in range(1,6):
  for kind,masks in [('row',range(1<<q)),('column',range(4))]:
   for mask in masks:
    for _ in range(10):full+=star_trial(q,kind,mask,rng);stars+=1
 cores=[(i,j) for i,j in product(range(8),repeat=2) if any((i>>a&1) and (j>>b&1) for a in range(3) for b in range(3) if a!=b)]
 thresholds=[scaling_trial(core,rng) for core in cores for _ in range(5)]
 symbolic()
 report={'star_core_exact_endpoint_checks':stars,'full_cover_rank_cases':full,'q_values':[1,2,3,4,5],'all_46_labeled_rank_two_cores_checked':len(cores)==46,'scaling_checks':len(thresholds),'leading_gap_degrees':[4,8,10,10],'symbolic_SOS_and_grading_checks':True,'computed_thresholds_verified':True,'max_sample_threshold':max(thresholds),'all_checks_passed':True,'seed':170522}
 (Path(__file__).resolve().parents[1]/'data'/'star_scaling_verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
