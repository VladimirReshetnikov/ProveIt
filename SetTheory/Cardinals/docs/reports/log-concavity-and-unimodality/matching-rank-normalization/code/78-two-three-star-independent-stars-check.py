#!/usr/bin/env python3
"""Independent core kernels, literal Hall supports and one-vertex gluing."""
if not __debug__:raise SystemExit('Run without -O.')
from itertools import combinations,permutations,product
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
import argparse,hashlib,json,time
import sympy as s
start=time.monotonic()
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-dir',type=Path,default=Path('/workspace/shared/incomplete-two-by-three-complete-exteriors'))
parser.add_argument('--output-dir',type=Path,default=Path(__file__).parent)
args=parser.parse_args()
u=s.symbols('u0:2');v=s.symbols('v0:3');L,M,N,R,S=s.symbols('L M N R S')
def prod(xs):
 out=1
 for x in xs:out*=x
 return out
def bits(mask):return [i for i in range(mask.bit_length()) if mask>>i&1]
def match(rows,tails,heads):
 mask=sum(1<<j for j in heads)
 for subset in range(1,1<<len(tails)):
  nb=0
  for i,a in enumerate(tails):
   if subset>>i&1:nb|=rows[a]&mask
  if nb.bit_count()<subset.bit_count():return False
 return True
def rank(rows,I,J):
 for k in range(min(len(I),len(J)),-1,-1):
  if any(match(rows,a,b) for a in combinations(I,k) for b in combinations(J,k)):return k
def support_masks(left,right,edges):
 # Relabel only for the Hall routine; physical labels stay in output masks.
 index={a:i for i,a in enumerate(right)}
 rows=[sum(1<<index[b] for aa,b in edges if aa==a) for a in left]
 out=[]
 for k in range(min(len(left),len(right))+1):
  for I in combinations(range(len(left)),k):
   for J in combinations(range(len(right)),k):
    if match(rows,I,J):out.append((sum(1<<left[i] for i in I)|sum(1<<right[j] for j in J),k))
 return out
def elementary(xs,top):
 out=[1]+[0]*top
 for x in xs:
  for k in range(top,0,-1):out[k]+=x*out[k-1]
 return out
def evaluate_supports(data,weights):
 out=[0]*6
 for used,k in data:out[k]+=prod(weights[i] for i in bits(used))
 return out
A=sum(u);B=prod(u);C=sum(v);D=sum(prod(x) for x in combinations(v,2));E=prod(v)
symbolic=0;weighted=0;gluing=0;star_masks=[];last_strict=0;degree_counts=Counter();all_orbits=set();star_orbits=set()
for mask in range(64):
 rows=[sum(1<<j for j in range(3) if mask>>(3*i+j)&1) for i in range(2)]
 rk=rank(rows,range(2),range(3))
 orbit=[]
 for pl in permutations(range(2)):
  for pr in permutations(range(3)):
   orbit.append(sum(1<<(3*pl[i]+pr[j]) for i in range(2) for j in range(3) if rows[i]>>j&1))
 all_orbits.add(min(orbit))
 if rk<=1:star_masks.append(mask);star_orbits.add(min(orbit))
 W11=sum(u[i]*v[j] for i in range(2) for j in range(3) if rows[i]>>j&1)
 W12=sum(u[i]*prod(v[j] for j in J) for i in range(2) for J in combinations(range(3),2) if any(rows[i]>>j&1 for j in J))
 W21=B*sum(v[j] for j in range(3) if any(rows[i]>>j&1 for i in range(2)))
 W13=E*sum(u[i] for i in range(2) if rows[i])
 W22=B*sum(prod(v[j] for j in J) for J in combinations(range(3),2) if any(rows[i]>>j&1 for i in range(2) for j in J))
 J22=B*sum(prod(v[j] for j in J) for J in combinations(range(3),2) if rank(rows,range(2),J)==2)
 J23=B*E*int(rk==2);W23=B*E*int(mask!=0)
 explicit=[1,A*R+C*L+W11,A*C*L*R+B*S+D*M+W12*L+W21*R+J22,A*D*M*R+B*C*L*S+E*N+W13*M+W22*L*R+J23*L,A*E*N*R+B*D*M*S+W23*M*R,B*E*N*S]
 boolean=[0]*6
 for im in range(4):
  for jm in range(8):
   I,J=bits(im),bits(jm);rr=rank(rows,I,J)
   for k in range(6):
    ix,iy=k-len(I),k-len(J);h=len(I)+len(J)-k
    if 0<=ix<=3 and 0<=iy<=2 and 0<=h<=rr:
     boolean[k]+=prod(u[i] for i in I)*prod(v[j] for j in J)*[1,L,M,N][ix]*[1,R,S][iy]
 assert all(s.expand(a-b)==0 for a,b in zip(boolean,explicit));symbolic+=1
 for nx,ny in product(range(4),range(3)):
  P=[0,1];Q=[2,3,4];X=list(range(5,5+nx));Y=list(range(5+nx,5+nx+ny));left=P+X;right=Q+Y
  edges={(i,2+j) for i in range(2) for j in range(3) if rows[i]>>j&1}|set(product(P,Y))|set(product(X,Q))
  data=support_masks(left,right,edges)
  for typ in range(3):
   weights=[1 if typ==0 else (i%4+1 if typ==1 else (0 if i%3==0 else F(i%5+1,i%3+1))) for i in range(5+nx+ny)]
   val=evaluate_supports(data,weights);ex=elementary([weights[i] for i in X],3);ey=elementary([weights[j] for j in Y],2)
   sub=dict(zip(u,weights[:2]));sub.update(dict(zip(v,weights[2:5])));sub.update({L:ex[1],M:ex[2],N:ex[3],R:ey[1],S:ey[2]})
   expected=[s.sympify(g).subs(sub) for g in explicit]
   assert all(s.Rational(a)==b for a,b in zip(val,expected));weighted+=1
   d=max(i for i,a in enumerate(val) if a);degree_counts[d]+=1
   if mask and d==5:
    assert 4*val[4]**2-10*val[3]*val[5]>0;last_strict+=1
  if rk<=1:
   if mask==0:
    l1,r1,l2,r2,shared=P,Y,X,Q,None
   else:
    incident=set.intersection(*({i,2+j} for i in range(2) for j in range(3) if rows[i]>>j&1))
    shared=min(incident)
    if shared in P:l1,r1,l2,r2=P,Y,[shared]+X,Q
    else:l1,r1,l2,r2=X,Q,P,Y+[shared]
   e1={(i,j) for i,j in edges if i in l1 and j in r1};e2={(i,j) for i,j in edges if i in l2 and j in r2}
   data1=support_masks(l1,r1,e1);data2=support_masks(l2,r2,e2)
   combined=Counter()
   for used1,k1 in data1:
    for used2,k2 in data2:
     if used1&used2:continue
     combined[(used1|used2,k1+k2)]+=1
   assert combined==Counter(data)
   gluing+=1
# Verify all seed bases directly for universal sets of size zero through eight.
seed_triples=0
for nx in range(9):
 # columns: exceptional p->{0,1}, d0,d1,d2, followed by universal copies
 rows=[3,1,2,4]+[7]*nx
 for I in combinations(range(nx+4),3):
  feasible=match(rows,I,[0,1,2]);assert feasible==(set(I)!={0,1,2});seed_triples+=1
m=s.symbols('m',integer=True,positive=True)
assert s.expand(9*(m*(m-1)/2)**2-12*m*(m*(m-1)*(m-2)/6)-m*m*(m-1)*(m+7)/4)==0
assert len(star_masks)==18 and len(star_orbits)==5 and len(all_orbits)==13
root=args.output_dir;source=args.source_dir
root.mkdir(parents=True,exist_ok=True)
rec={'verdict':'PASS','core_kernel_masks':symbolic,'weighted_Hall_cases':weighted,'actual_degree_counts':dict(sorted(degree_counts.items())),'star_masks':len(star_masks),'star_orbits':len(star_orbits),'all_core_orbits':len(all_orbits),'formal_support_gluing_identities':gluing,'rank_five_strict_last_checks':last_strict,'exceptional_seed_Hall_triples':seed_triples,'symbolic_discriminant':'PASS','elapsed_seconds':round(time.monotonic()-start,3),'source_sha256':{n:hashlib.sha256((source/n).read_bytes()).hexdigest() for n in ['STAR_CORE_REAL_ROOTEDNESS.md','CORE_KERNEL_AND_LAST_GAP.md']}}
(root/'independent_receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
