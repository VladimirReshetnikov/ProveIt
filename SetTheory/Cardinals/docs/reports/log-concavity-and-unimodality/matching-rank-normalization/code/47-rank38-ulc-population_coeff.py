from math import comb
from functools import lru_cache

def choose(n,k):
    return comb(n,k) if 0 <= k <= n else 0

@lru_cache(None)
def T(a,n,k,q):
    return sum(choose(a,i)*choose(n,k-i) for i in range(max(q,0),min(a,k)+1)) if q>=0 else 0

def population_coefficient(a,b,n,k,s,p):
    r=a+b;L=2*k-s
    if L<2*p:return 0
    total=0
    for j in range(max(0,s-b),min(b,s)+1):
        wt=comb(b,j)*comb(b,s-j)
        square=choose(L-2*p,k-j-p)*T(a,n,k,k-j)*T(a,n,k,k-s+j)
        adjacent=choose(L-2*p,k-1-j-p)*T(a,n,k-1,k-1-j)*T(a,n,k+1,k+1-s+j)
        total+=wt*(k*(r-k)*square-(k+1)*(r-k+1)*adjacent)
    return choose(L-p,p)*total

