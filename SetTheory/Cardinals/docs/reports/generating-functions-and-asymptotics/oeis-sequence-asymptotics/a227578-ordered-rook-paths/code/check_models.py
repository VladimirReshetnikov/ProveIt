from functools import lru_cache
from math import prod
import json
@lru_cache(None)
def rook(l):
 if not any(l): return 1
 return sum(rook(l[:i]+(j,)+l[i+1:]) for i,x in enumerate(l) for j in range(l[i-1] if i else 0,x))
@lru_cache(None)
def words(l,last):
 if not any(l):return 1
 ans=0
 for i,x in enumerate(l):
  if x and (i==0 or x>l[i-1]):
   v=l[:i]+(x-1,)+l[i+1:]
   ans+=(2 if last==i else 1)*words(v,i)
 return ans
out=[]
for k in range(1,6):
 for n in range(9):
  a=rook((n,)*k);b=words((n,)*k,-1)
  assert a==b
  out.append(dict(n=n,k=k,rook=a,unit_adjacency=b))
print(json.dumps(out,indent=2))
