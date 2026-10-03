from functools import lru_cache
from block_formula import block_Q
from state_search import f
N=20
@lru_cache(None)
def step_terms(L,q):
 return [(r,sum(block_Q(ell,q,r) for ell in range(L))) for r in range(L)]
@lru_cache(None)
def walk(n,h):
 if n==0:return 1
 ans=1
 for L in range(1,n+1):
  for q in range(1,h+1):
   for r,v in step_terms(L,q):
    if v:ans+=v*walk(n-L,h+1-q+r)
 return ans
known=[1,1,2,5,14,42,133,442,1535,5546,20754,80113,317875,1292648,5374073,22794182,98462847,432498659,1929221610,8728815103,40017844229]
for n in range(N+1):
 v=1 if n==0 else walk(n-1,1)
 assert v==known[n]
 assert v==(1 if n==0 else f(n-1,0,0,(0,)))
 print(n,v,'PASS',flush=True)
print('PASS independent binomial jump walk, normalized-state recurrence, and OEIS initial terms all agree through n=20')
