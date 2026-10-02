from math import comb
from fractions import Fraction
from functools import lru_cache

def C(j,k):return comb(j+k-1,k)*comb(j+k,k+1)//j

def block_Q(ell,q,r):
 if ell==0:return int(r==0)
 return sum(C(j,k)*comb(j,r-k)*comb(j+ell-2,ell-r-k-1)
  for j in range(1,q+1) for k in range(r+1)
  if 0<=r-k<=j and ell>=r+k+1)

if __name__=='__main__':
 # Compare the exact formula with independently computed gap operators.
 exec(open(__file__.replace('block_formula.py','check_operators.py')).read().split('checks=0')[0])
 for q in range(1,9):
  for ell in range(0,N+1):
   for r in range(N+1):
    got=block_Q(ell,q,r)
    assert got==Q[q].get((ell,r),0),(ell,q,r,got,Q[q].get((ell,r),0))
 print('PASS closed binomial jump coefficients against operator recurrence')
