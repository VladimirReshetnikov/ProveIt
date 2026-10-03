"""Exact polynomial checks of the two conditioning reductions."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import prod
from pathlib import Path
import random,json
rng=random.Random(500349)
def polynomial(cols,lw,rw,forced=()):
 ans=[F(0)]*(min(len(lw),len(cols))+1)
 forcedmask=sum(1<<i for i in forced)
 dp={0:{0}}
 for J in range(1<<len(cols)):
  if J:
   bit=J&-J;j=bit.bit_length()-1;states=set()
   for I in dp[J^bit]:
    available=cols[j]&~I
    while available:
     b=available&-available;available-=b;states.add(I|b)
   dp[J]=states
  k=J.bit_count()
  if J&forcedmask!=forcedmask or k>=len(ans):continue
  ans[k]=ans[k]+prod(rw[j]for j in range(len(cols))if J>>j&1)*sum(prod(w for i,w in enumerate(lw)if I>>i&1)for I in dp[J])
 return ans
for case in range(100):
 n=6;m=5;cols=[3]+[rng.randrange(1,1<<n)for _ in range(m-1)]
 lw=list(map(F,[rng.randrange(1,6)for _ in range(n)]));rw=list(map(F,[rng.randrange(1,6)for _ in range(m)]))
 P=polynomial(cols,lw,rw,(0,))
 merged=[int(bool(c&3))|((c>>2)<<1)for c in cols[1:]]
 newlw=[lw[0]*lw[1]/(lw[0]+lw[1])]+lw[2:]
 H=polynomial(merged,newlw,rw[1:]);rhs=[F(0)]+[rw[0]*(lw[0]+lw[1])*h for h in H]
 while len(P)<len(rhs):P.append(F(0))
 while len(rhs)<len(P):rhs.append(F(0))
 assert P==rhs
@lru_cache(None)
def match(types,allowed=7):
 if not types:return True
 r=types[0]&allowed
 return any(match(types[1:],allowed^b)for b in(1,2,4)if r&b)
for case in range(100):
 n=5
 while True:
  L=[rng.randrange(1,8)for _ in range(n)]
  if any(match(tuple(L[i]for i in I))for I in combinations(range(n),3)):break
 core=[rng.randrange(8)for _ in range(3)]
 forcedR=rng.choice([(1,2),(3,5),(3,3),(7,7),(2,5),(1,7)])
 remR=[1,2,3,4,5,6,7]
 aw=[F(rng.randrange(1,6))for _ in range(3)];lw=[F(rng.randrange(1,6))for _ in L]
 bw=[F(rng.randrange(1,6))for _ in range(3)];fw=[F(rng.randrange(1,6))for _ in forcedR];rw=[F(rng.randrange(1,6))for _ in remR]
 E=sum(prod(aw[i]for i in I)for I in combinations(range(3),2)if match(forcedR,sum(1<<i for i in I)))
 S=0
 for i in range(3):
  if match(forcedR,7^(1<<i)):S|=core[i]
 W=sum(w for t,w in zip(remR,rw)if match(forcedR+(t,)))
 cols=[sum(1<<i for i,t in enumerate(core+L)if t>>b&1)for b in range(3)]+list(forcedR)+remR
 P=polynomial(cols,aw+lw,bw+fw+rw,(3,4))
 hcols=[sum(1<<i for i,t in enumerate(L+[S])if t>>b&1)for b in range(3)]+[1<<n]
 H=polynomial(hcols,lw+[prod(aw)/E],bw+[W]);rhs=[F(0)]*2+[prod(fw)*E*h for h in H]
 while len(P)<len(rhs):P.append(F(0))
 while len(rhs)<len(P):rhs.append(F(0))
 assert P==rhs,(core,L,forcedR,P,rhs)
 assert max(i for i,x in enumerate(H)if x)==4
out={'degree_two_merge_polynomial_checks':100,'two_exterior_forced_rank_four_reduction_checks':100,'arbitrary_positive_fields_on_both_shores':True,'all_checks_passed':True}
(Path(__file__).resolve().parents[1]/'data'/'reduction_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
