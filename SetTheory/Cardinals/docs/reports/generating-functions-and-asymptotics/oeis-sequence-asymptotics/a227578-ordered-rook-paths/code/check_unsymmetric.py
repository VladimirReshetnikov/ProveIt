from itertools import permutations,product
from functools import lru_cache
from math import comb
@lru_cache(None)
def unrestricted(l):
 if not any(l):return 1
 return sum(unrestricted(l[:i]+(j,)+l[i+1:]) for i,v in enumerate(l) for j in range(v))
@lru_cache(None)
def rook(l):
 if not any(l):return 1
 return sum(rook(l[:i]+(j,)+l[i+1:]) for i,v in enumerate(l) for j in range(l[i-1] if i else 0,v))
def formula(n,k):
 ans=0
 for perm in permutations(range(k)):
  sg=(-1)**sum(perm[i]>perm[j] for i in range(k) for j in range(i+1,k))
  # Delta descending powers k-i, so permutation columns power k-1-perm[i]
  targets=[n+k-1-i-(k-1-perm[i]) for i in range(k)]
  if min(targets)<0:continue
  for js in product(*(range(v+1) if i else [0] for i,v in enumerate(targets))):
   w=1
   for i,j in enumerate(js):
    if i:w*=comb(i+j-1,j)
   ans+=sg*w*unrestricted(tuple(v-j for v,j in zip(targets,js)))
 return ans
for k in range(2,5):
 for n in range(5):
  f=formula(n,k);a=rook((n,)*k);print(k,n,f,a,f==a);assert f==a
