from pathlib import Path
from itertools import combinations, combinations_with_replacement, permutations
from functools import lru_cache
from collections import Counter
import sys,json,hashlib
import sympy as s
ROOT=Path(__file__).resolve().parent.parent
N=s.symbols('N1:8');types=(1,2,3,5,6,7)
@lru_cache(None)
def match(rows):
 return any(all(mask>>c&1 for mask,c in zip(rows,assignment)) for assignment in permutations(range(len(rows))))
@lru_cache(None)
def wt(ls):
 result=s.Poly(1,N,domain=s.QQ)
 for t,k in Counter(ls).items():
  for j in range(k):result*=s.Poly(N[t-1]-j,N)
  result=result.mul_ground(s.Rational(1,s.factorial(k)))
 return result
@lru_cache(None)
def endpoint(core,S):
 degree=3 if S==0 else 4
 ans=s.Poly(0,N,domain=s.QQ)
 for k in range(4):
  for selected in combinations(range(3),k):
   ar=tuple(sum(((core[j]>>i)&1)<<j for j in range(3)) + (0 if S==0 else ((S>>i)&1)<<3) for i in selected)
   for ls in combinations_with_replacement(types,degree-k):
    if match(ar+ls):ans+=wt(ls)
 return ans
