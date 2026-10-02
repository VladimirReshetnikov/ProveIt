from itertools import permutations,product
from math import comb,factorial
from collections import defaultdict
from functools import lru_cache
import json
@lru_cache(None)
def count(a):
 if sum(a)==0:return 1
 return sum(count(a[:i]+(v,)+a[i+1:]) for i in range(len(a)) for v in range(a[i+1] if i+1<len(a) else 0,a[i]))
def symformula(n,k):
 N=n+k-1
 # Smooth series T=prod(1-x_i)^-(k-1)/(1-sum x_i/(1-x_i)).
 T={}
 for a in product(range(N+1),repeat=k):
  T[a]= __import__('functools').reduce(lambda x,y:x*y,(comb(k-2+v,v) for v in a),1)+sum(T[a[:i]+(v,)+a[i+1:]] for i in range(k) for v in range(a[i]))
 d=[]
 for a in permutations(range(k)):
  sign=(-1)**sum(a[i]>a[j] for i in range(k) for j in range(i+1,k))
  d.append((a,sign))
 # Ascending Vandermonde has same square as descending.
 total=0
 for a,sa in d:
  for b,sb in d:
   rem=tuple(N-a[i]-b[i] for i in range(k))
   if min(rem)>=0:total+=sa*sb*T[rem]
 assert total%factorial(k)==0
 return (-1)**(k*(k-1)//2)*total//factorial(k)
out=[]
for k,ns in [(2,range(7)),(3,range(6)),(4,range(5)),(5,range(4))]:
 for n in ns:
  f=symformula(n,k);a=count((n,)*k)
  out.append(dict(k=k,n=n,symmetric=f,direct=a,equal=f==a))
  print(k,n,f,a,f==a,flush=True)
assert all(r['equal'] for r in out)
open('symmetric-checks.json','w').write(json.dumps(out,indent=2)+'\n')
