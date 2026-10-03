"""Independent direct-support regressions for the two population identities."""
from math import comb
from random import Random
from pathlib import Path
import json
from population_coeff import population_coefficient
from difference_coeff import finite_differences

def c(n,k):
    return comb(n,k) if 0<=k<=n else 0

def support_coefficient(a,b,n,m,k,j):
    # Count selected original core-left vertices directly.
    return c(b,j)*c(m,k-j)*sum(c(a,i)*c(n,k-i) for i in range(a+1) if i+j>=k)

def run():
    rng=Random(61371)
    checked=0
    for _ in range(200):
        a=rng.randrange(3,10);b=rng.randrange(3,10)
        n=b+rng.randrange(35);m=a+rng.randrange(35)
        r=a+b;k=rng.randrange(2,r-1)
        s=rng.randrange(max(0,2*k-2*a),min(2*b,2*k)+1)
        L=2*k-s
        def v(kk,j):return support_coefficient(a,b,n,m,kk,j)
        direct=k*(r-k)*sum(v(k,j)*v(k,s-j) for j in range(b+1))
        direct-=(k+1)*(r-k+1)*sum(v(k-1,j)*v(k+1,s-j) for j in range(b+1))
        expansion=0
        for p in range(L//2+1):
            vals=[population_coefficient(a,b,b+i,k,s,p) for i in range(s+1)]
            ds=finite_differences(vals)
            gn=sum(z*c(n-b,e) for e,z in enumerate(ds))
            assert gn==population_coefficient(a,b,n,k,s,p)
            expansion+=c(m,L-p)*gn
        assert expansion==direct,(a,b,n,m,k,s,expansion,direct)
        checked+=1
    return {'exact_direct_support_regressions':checked,'all_passed':True}

if __name__=='__main__':
    result=run()
    print(json.dumps(result,indent=2))
