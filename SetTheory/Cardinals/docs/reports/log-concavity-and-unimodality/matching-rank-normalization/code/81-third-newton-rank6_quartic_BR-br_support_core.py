"""Exact Hall-support polynomials and integer population translations."""
from itertools import combinations,combinations_with_replacement
from functools import lru_cache
from collections import Counter
from math import comb
import sympy as s
Ns=s.symbols('N1:8')
@lru_cache(None)
def hall(rows):
 """Rows have equal size to the selected column set; masks label its columns."""
 for size in range(1,len(rows)+1):
  for chosen in combinations(rows,size):
   union=0
   for mask in chosen:union|=mask
   if union.bit_count()<size:return False
 return True

@lru_cache(None)
def minor_count(columns):
 return sum(hall(tuple(sum((1<<j) for j,c in enumerate(columns) if c>>i&1) for i in aset)) for aset in combinations(range(3),len(columns)))

@lru_cache(None)
def falling_choose(x,j):
 v=s.Integer(1)
 for i in range(j):v*=x-i
 return s.expand(v/s.factorial(j))

@lru_cache(None)
def endpoint(core,columns):
 """Polynomial weighted count of row supports for fixed selected columns."""
 degree=len(columns);answer=0
 for ca in range(min(3,degree)+1):
  for aset in combinations(range(3),ca):
   arows=tuple(sum(1<<j for j,(kind,v) in enumerate(columns) if ((core[v] if kind=='B' else v)>>i)&1) for i in aset)
   for ls in combinations_with_replacement(range(1,8),degree-ca):
    lrows=tuple(sum(1<<j for j,(kind,v) in enumerate(columns) if kind=='B' and mask>>v&1) for mask in ls)
    if not hall(arows+lrows):continue
    weight=s.Integer(1)
    for mask,mult in Counter(ls).items():weight*=falling_choose(Ns[mask-1],mult)
    answer+=weight
 return s.expand(answer)

def translate(poly,basis):
 # Translate each distinct coordinate by its full multiplicity, in descending
 # coordinate order; this differs from the producer's repeated +1 prefix cache.
 out=poly
 for i,b in sorted(Counter(x-1 for x in basis).items(),reverse=True):
  new={}
  for ex,c in out.items():
   for j in range(ex[i]+1):
    ee=list(ex);ee[i]=j;ee=tuple(ee)
    new[ee]=new.get(ee,0)+c*comb(ex[i],j)*b**(ex[i]-j)
  out={e:c for e,c in new.items() if c}
 return out

BASES=tuple(ms for ms in combinations_with_replacement(range(1,8),3) if hall(ms))
if len(BASES)!=51:raise RuntimeError('basis count')
