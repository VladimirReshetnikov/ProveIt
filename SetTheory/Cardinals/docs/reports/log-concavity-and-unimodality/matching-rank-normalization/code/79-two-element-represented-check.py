#!/usr/bin/env python3
"""Independent symbolic and representable-matroid checks for full selected-tail Lorentzianity."""
if not __debug__:raise SystemExit('Run without -O.')
from pathlib import Path
from itertools import combinations,product
from collections import defaultdict,Counter
from math import prod
import argparse,hashlib,json,time
import sympy as s
p=argparse.ArgumentParser();p.add_argument('--source-note',type=Path,default=Path('/workspace/shared/full-selected-tail-lorentzian/FULL_SELECTED_TAIL_THEOREM.md'));p.add_argument('--output-dir',type=Path,default=Path(__file__).parent);args=p.parse_args();started=time.monotonic()
a,b,z,u,L0,L1,H,S=s.symbols('a b z u L0 L1 H S');R0=L0+H;R1=L1+H;M=L0*L1+H*(L0+L1)+S;MM=L0*L1+H*(L0+L1)+H*H/2
q0=z*z+(a*R0+b*R1)*z+a*b*M
assert s.expand(s.hessian(q0,(a,b,z)).det()-2*M*(H*H-S))==0
rank1=0
for alpha,beta in product([0,1],repeat=2):
 W=L1*alpha+L0*beta+H*max(alpha,beta)
 F=q0*u+z*z*(a*alpha+b*beta)+a*b*z*W
 ha=s.hessian(s.diff(F,a),(u,z,b));assert ha==s.Matrix([[0,R0,M],[R0,2*alpha,W],[M,W,0]])
 assert s.expand(ha.det()-2*M*(R0*W-alpha*M))==0
 assert s.expand(R0*W-alpha*M-alpha*(H*H-S)-(1-alpha)*beta*R0**2-alpha*beta*R0*L0)==0
 hz=s.hessian(s.diff(F,z),(u,z,a,b));schur=hz[2:,2:]-hz[2:,:2]*hz[:2,:2].inv()*hz[:2,2:]
 expected=s.Matrix([[-2*R0*alpha,-H*alpha*beta],[-H*alpha*beta,-2*R1*beta]])
 assert (schur-expected).applyfunc(s.expand)==s.zeros(2);rank1+=1
U0,UA,UB,UU,V=s.symbols('U0 UA UB U V');sa,sb,sy=s.symbols('sa sb sy');J=s.Matrix([[0,1,1],[1,0,1],[1,1,1]]);m=s.Matrix([L1,L0,H]);ss=s.Matrix([sa,sb,sy]);W=L1*UA+L0*UB+H*UU
seed=U0+sa*UA+sb*UB+sy*UU+(sa*sb+sa*sy+sb*sy+sy*sy/2)*V
F=z*z*U0+z*(a*R0+b*R1)*U0+a*b*M*U0+z*z*(a*UA+b*UB)+a*b*z*W+a*b*z*z*V
subseed=lambda vals:seed.subs(dict(zip((sa,sb,sy),vals)),simultaneous=True)
identities=[(s.diff(F,z,2),2*subseed([a,b,0])),(s.diff(F,a,b),M*subseed(m*z/M)-(MM-M)*z*z*V/M),(s.diff(F,a,z),R0*subseed((2*s.Matrix([1,0,0])*z+m*b)/R0)-MM*b*b*V/R0),(s.diff(F,b,z),R1*subseed((2*s.Matrix([0,1,0])*z+m*a)/R1)-MM*a*a*V/R1),(s.diff(F,a,z,2),2*(UA+b*V)),(s.diff(F,b,z,2),2*(UB+a*V)),(s.diff(F,a,b,z),W+2*z*V),(s.diff(F,a,b,z,2),2*V)]
for left,right in identities:assert s.cancel(left-right)==0
assert s.expand(sum(m[i]*s.diff(seed,ss[i])for i in range(3))-W-(m.T*J*ss)[0]*V)==0

def subsets(m,k):return []if k<0 else combinations(range(m),k)
def families(R):
 q=R.rows;m=R.cols-2
 def valid(cols):return len(cols)==q and (q==0 or R[:,list(cols)].det()!=0)
 u0={sum(1<<i for i in I)for I in subsets(m,q)if valid(I)}
 ua={sum(1<<i for i in I)for I in subsets(m,q-1)if valid(tuple(I)+(m,))}
 ub={sum(1<<i for i in I)for I in subsets(m,q-1)if valid(tuple(I)+(m+1,))}
 vv={sum(1<<i for i in I)for I in subsets(m,q-2)if valid(tuple(I)+(m,m+1))}
 return u0,ua,ub,ua|ub,vv

def formula(R,pops):
 q=R.rows;m=R.cols-2;u0,ua,ub,uu,vv=families(R);l0=sum(w for typ,w in pops if typ==1);l1=sum(w for typ,w in pops if typ==2);weights=[w for typ,w in pops if typ==3];hh=sum(weights);sv=sum(x*y for x,y in combinations(weights,2));r0=l0+hh;r1=l1+hh;mm=l0*l1+hh*(l0+l1)+sv;out=defaultdict(int)
 def add(fam,pa,pb,pz,coef):
  for mask in fam:out[(pa,pb,pz)+tuple(int(mask>>i&1)for i in range(m))]+=coef
 add(u0,0,0,2,1);add(u0,1,0,1,r0);add(u0,0,1,1,r1);add(u0,1,1,0,mm);add(ua,1,0,2,1);add(ub,0,1,2,1);add(ua,1,1,1,l1);add(ub,1,1,1,l0);add(uu,1,1,1,hh);add(vv,1,1,2,1)
 return {k:v for k,v in out.items()if v}
def augmentation(R,pops):
 q=R.rows;m=R.cols-2;n=len(pops);big=s.zeros(q+n,m+2+n);big[:q,:m+2]=R
 for j,(typ,w)in enumerate(pops):
  if typ&1:big[q+j,m]=s.Symbol(f'ya{j}')
  if typ&2:big[q+j,m+1]=s.Symbol(f'yb{j}')
  big[q+j,m+2+j]=1
 out=defaultdict(int);count=0
 for chosen in combinations(range(big.cols),q+n):
  count+=1;det=1 if q+n==0 else big[:,list(chosen)].det(method='domain-ge')
  if det==0:continue
  missing=[j for j in range(n)if m+2+j not in chosen];assert len(missing)<=2
  key=(int(m in chosen),int(m+1 in chosen),2-len(missing))+tuple(int(i in chosen)for i in range(m))
  out[key]+=prod(pops[j][1]for j in missing)
 return {k:v for k,v in out.items()if v},count

def contracted(R,e):
 q=R.rows;m=R.cols-2;v=R[:,e]
 if not any(v):return None
 pivot=next(i for i in range(q)if v[i]);rows=[R[j,:]-v[j]/v[pivot]*R[pivot,:]for j in range(q)if j!=pivot]
 Q=s.Matrix.vstack(*rows)if rows else s.zeros(0,R.cols)
 keep=[i for i in range(m)if i!=e]+[m,m+1]
 return Q[:,keep]
def derivative(poly,e):
 out={}
 for key,value in poly.items():
  if key[3+e]:out[key[:3+e]+key[4+e:]]=value
 return out
matroids=[]
# Rational representations, including loops, parallel distinguished columns and dependent old elements.
for q in range(5):
 if q==0:matroids.append(s.zeros(0,3));continue
 old=[s.eye(q)[:,i]for i in range(q)]+[s.ones(q,1),s.zeros(q,1)]
 choices=[s.zeros(q,1),s.eye(q)[:,0],s.ones(q,1),s.Matrix(list(range(1,q+1)))]
 pairs=list(product(range(4),repeat=2))if q==1 else [(0,0),(0,1),(1,1),(1,2),(2,3)]
 for aa,bb in pairs:matroids.append(s.Matrix.hstack(*old,choices[aa],choices[bb]))
populations=[[],[(1,2)],[(2,3)],[(3,1)],[(1,2),(2,3)],[(1,2),(3,1)],[(2,3),(3,2)],[(3,1),(3,2)],[(1,2),(2,3),(3,1)],[(3,0),(3,1)]]
augmentation_checks=contraction_checks=basis_tests=0;rank_counts=Counter()
for idx,R in enumerate(matroids):
 assert R[:,:R.cols-2].rank()==R.rows
 for pops in populations:
  expected=formula(R,pops)
  # Augmentation is checked on all low-rank cases and representative higher-rank matrices.
  if R.rows<=2 or idx%3==0:
   actual,n=augmentation(R,pops);assert actual==expected,(R,pops,actual,expected);augmentation_checks+=1;basis_tests+=n
  for e in range(R.cols-2):
   Q=contracted(R,e);actual=derivative(expected,e)
   if Q is None:assert not actual
   else:
    assert Q[:,:Q.cols-2].rank()==Q.rows
    assert actual==formula(Q,pops),(R,e,pops)
   contraction_checks+=1
  rank_counts[R.rows]+=1
receipt={'verdict':'PASS','source_sha256':hashlib.sha256(args.source_note.read_bytes()).hexdigest(),'q0_Hessian_determinant':True,'rank1_indicator_cases':rank1,'rank2_to_rank4_derivative_identities':len(identities),'directional_derivative_identity':True,'rational_representable_matroids':len(matroids),'population_specializations_by_rank':dict(sorted(rank_counts.items())),'literal_symbolic_augmentation_identities':augmentation_checks,'augmented_candidate_bases_tested':basis_tests,'old_element_contraction_identities':contraction_checks,'zero_population_weights_included':True,'finite_checks_are_supplementary':True,'elapsed_seconds':round(time.monotonic()-started,3)}
args.output_dir.mkdir(parents=True,exist_ok=True);(args.output_dir/'independent_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
