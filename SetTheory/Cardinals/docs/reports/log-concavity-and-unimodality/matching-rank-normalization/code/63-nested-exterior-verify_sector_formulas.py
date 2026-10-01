"""Independent endpoint enumeration and rank-three sector formulas."""
from itertools import combinations
from functools import lru_cache
from math import prod
from pathlib import Path
import random,json
rng=random.Random(917030)
@lru_cache(None)
def match(rows):
 if not rows:return True
 r=rows[0]
 return any(match(tuple(sorted(x&~b for x in rows[1:])))for b in(1,2,4)if r&b)
def mat(rows,allowed=7):return match(tuple(sorted(r&allowed for r in rows)))
def exterior(types,Aset=7):return mat(types,Aset)
def value(ids,weights):return prod(weights[i]for i in ids)
def families(L,core):
 T=[I for I in combinations(range(len(L)),3)if mat(tuple(L[i]for i in I))]
 P=[set(I for I in combinations(range(len(L)),2)if mat((row,)+tuple(L[i]for i in I)))for row in core]
 return T,P

def direct(core,L,forcedB,forcedR,remR,leftweights,remweights,Bweights):
 cols=[sum(1<<i for i,t in enumerate(core+L)if t>>b&1)for b in range(3)]+list(forcedR)+list(remR)
 forced=tuple(forcedB)+tuple(range(3,3+len(forcedR)))
 others=[b for b in range(3)if b not in forcedB]+list(range(3+len(forcedR),len(cols)))
 weights={b:Bweights[b]for b in range(3)}
 weights.update({3+len(forcedR)+i:w for i,w in enumerate(remweights)})
 def count(J):
  states={0}
  for j in J:
   out=set()
   for I in states:
    available=cols[j]&~I
    while available:
     bit=available&-available;available-=bit;out.add(I|bit)
   states=out
  return sum(prod(w for i,w in enumerate(leftweights)if I>>i&1)for I in states)
 return [sum(count(forced+extra)*prod(weights[i]for i in extra)for extra in combinations(others,d))for d in range(3)]

counts={'degree3_unit':0,'degree2_weighted_L':0,'two_B_two_R_arbitrary_fields':0,'singleton_R_weighted_L':0}
for trial in range(180):
 n=rng.randrange(3,8)
 while True:
  L=[rng.randrange(1,8)for _ in range(n)]
  if any(mat(tuple(L[i]for i in I))for I in combinations(range(n),3)):break
 core=[rng.randrange(8)for _ in range(3)]
 R=list(range(1,8));rw=[rng.randrange(1,6)for _ in R]
 for deg in (2,3):
  lw=[1]*n if deg==3 else [rng.randrange(1,5)for _ in L]
  T0,Pi=families(L,core);T=sum(value(I,lw)for I in T0)
  if deg==3:
   Wset=set.union(*Pi);W=sum(value(I,lw)for I in Wset)
   a=[sum(value(I,lw)for I in Pi[k]-set.union(*(Pi[j]for j in range(3)if j!=k)))for k in range(3)]
   V=sum(lw[i]for i,t in enumerate(L)if any(mat((t,core[j],core[k]))for j,k in combinations(range(3),2)))
   C=3*T+3*W-sum(a)+V
   costs=[2*T+W-a[(t.bit_length()-1)]if t.bit_count()==1 else 3*T+W for t in R]
   forcedR=[7]
   assert T>=n-2 and V<=T+2
  else:
   union=core[0]|core[1]
   Uset=set(I for I in combinations(range(n),2)if mat((union,)+tuple(L[i]for i in I)))
   Pset=Pi[2];U=sum(value(I,lw)for I in Uset);P=sum(value(I,lw)for I in Pset);W=sum(value(I,lw)for I in Uset|Pset)
   O=sum(value(I,lw)for I in Uset&Pset)
   V=sum(lw[i]for i,t in enumerate(L)if mat((t,union,core[2])))
   assert 4*U*P-2*O*O>=3*T*V
   C=2*T+U+2*P+V
   costs=[T+P if t&4==0 else 2*T+U if t==4 else 3*T+W for t in R]
   forcedR=[3]
  c1=sum(w*q for w,q in zip(rw,costs))
  c2=T*sum(rw[i]*rw[j]for i,j in combinations(range(7),2)if exterior(forcedR+[R[i],R[j]]))
  got=direct(core,L,(0,1,2),forcedR,R,[1]*3+lw,rw,[1]*3)
  assert got==[C,c1,c2],(deg,core,L,got,[C,c1,c2])
  assert c1*c1>=3*C*c2
  counts['degree3_unit'if deg==3 else'degree2_weighted_L']+=1
 # Two B + two R, all left fields arbitrary.
 lw=[rng.randrange(1,5)for _ in L];aw=[rng.randrange(1,5)for _ in range(3)]
 J=tuple(sorted(rng.sample(range(3),2)));missing=next(b for b in range(3)if b not in J);z=rng.randrange(1,6)
 forcedR=rng.choice([[1,2],[3,5],[7,7],[1,7],[3,3],[2,5]])
 allowed=sum(1<<b for b in J)
 E=sum(value(I,aw)for I in combinations(range(3),2)if exterior(forcedR,sum(1<<i for i in I)))
 Ap=prod(aw);S=0
 for i in range(3):
  if exterior(forcedR,7^(1<<i)):S|=core[i]
 b=sum(value(I,lw)for I in combinations(range(n),2)if mat(tuple(L[i]for i in I),allowed))
 c=sum(value(I,lw)for I in combinations(range(n),3)if mat(tuple(L[i]for i in I)))
 V=sum(lw[i]for i,t in enumerate(L)if mat((t,S),allowed))
 U=sum(value(I,lw)for I in combinations(range(n),2)if mat((S,)+tuple(L[i]for i in I)))
 W=sum(w for t,w in zip(R,rw)if exterior(forcedR+[t]))
 want=[E*b+Ap*V,(E*c+Ap*U)*z+Ap*b*W,Ap*c*z*W]
 Bw=[1]*3;Bw[missing]=z
 got=direct(core,L,J,forcedR,R,aw+lw,rw,Bw)
 assert got==want,(core,L,J,forcedR,got,want)
 assert b*U>=c*V and got[1]**2>=4*got[0]*got[2]
 counts['two_B_two_R_arbitrary_fields']+=1
 # Forced singleton R at A1: delete that forced endpoint and count the two-row reduction.
 T0,Pi=families(L,core);T=sum(value(I,lw)for I in T0)
 U=sum(value(I,lw)for I in Pi[1]);P=sum(value(I,lw)for I in Pi[2]);W0=sum(value(I,lw)for I in Pi[1]|Pi[2]);O=sum(value(I,lw)for I in Pi[1]&Pi[2])
 V=sum(lw[i]for i,t in enumerate(L)if mat((t,core[1],core[2])))
 C=T+U+P+V
 costs=[0 if t>>1==0 else T+P if t>>1==1 else T+U if t>>1==2 else 2*T+W0 for t in R]
 c1=sum(w*q for w,q in zip(rw,costs))
 c2=T*sum(rw[i]*rw[j]for i,j in combinations(range(7),2)if exterior([1,R[i],R[j]]))
 got=direct(core,L,(0,1,2),[1],R,[1]*3+lw,rw,[1]*3)
 assert got==[C,c1,c2] and c1*c1>=3*C*c2
 assert 4*U*P-2*O*O>=3*T*V
 counts['singleton_R_weighted_L']+=1
out={'counts':counts,'all_support_formulas_match_independent_endpoint_enumeration':True,'all_bound_checks_passed':True,'scope':'Exact finite regression checks; universal proof audited separately'}
(Path(__file__).resolve().parents[1]/'data'/'sector_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
