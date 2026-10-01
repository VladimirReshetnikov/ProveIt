"""Exact regression checks for every-full-core-shape obstruction formulas.

The proof is algebraic. Finite tests independently count support macrostates
using a Boolean perfect-matching oracle, not matching multiplicities.
"""
from math import comb, gcd, isqrt
from functools import lru_cache
from pathlib import Path
import json

@lru_cache(None)
def has_pm(rows):
    if not rows:return True
    row=min(rows,key=int.bit_count)
    if not row:return False
    rest=list(rows);rest.remove(row)
    while row:
        bit=row&-row;row-=bit
        if has_pm(tuple(v&~bit for v in rest)):return True
    return False

def parameters(a,b,universal=False):
    r=a+b;K=(r-1)*a*b;H=(r+1)*a*b-2*r*(r-1)
    assert H>0 and 15*H>=K
    t=31 if universal else 1+(2*K+H-1)//H
    N=b-1+t;M=a-1+t
    assert K*(2*t+1)<H*t*t
    return r,K,H,t,N,M

def tail(a,b,N,M):
    r=a+b
    A=[comb(N,b-i)for i in range(3)]
    B=[comb(M,a-i)for i in range(3)]
    X=a*A[0]*B[1]+b*A[1]*B[0]
    Y=a*A[1]*B[2]+b*A[2]*B[1]
    Z=comb(a,2)*A[0]*B[2]+a*b*A[1]*B[1]+comb(b,2)*A[2]*B[0]
    alpha=(r-1)*A[1]**2*B[1]**2-2*r*A[0]*A[2]*B[0]*B[2]
    beta=2*(r-1)*A[1]*B[1]*X-2*r*A[0]*B[0]*Y
    gamma=(r-1)*X**2-2*r*A[0]*B[0]*Z
    return A,B,X,Y,Z,alpha,beta,gamma

def endpoint_threshold(alpha,beta,gamma):
    assert alpha<0 and beta>0 and gamma>0
    aa=-alpha
    w=1+(beta+isqrt(beta*beta+4*aa*gamma))//(2*aa)
    q=lambda v:alpha*v*v+beta*v+gamma
    assert q(w)<0 and q(w-1)>=0
    return w

def independent_counts(a,b,N,M,w):
    r=a+b;p=[0]*(r+1)
    for i in range(a+1):
        for j in range(b+1):
            for l in range(b+1):
                k=i+l
                for rho in range(a+1):
                    if k!=j+rho:continue
                    rows=[(1<<(j+rho))-1]*i+[(1<<j)-1]*l
                    if has_pm(tuple(rows)):
                        p[k]+=comb(a,i)*comb(b,j)*comb(N,l)*comb(M,rho)*w**(i+j)
    return p

records=[]
for a,b in ((3,3),(3,4),(3,5),(4,4),(4,5),(5,5),(3,8)):
    r,K,H,t,N,M=parameters(a,b)
    A,B,X,Y,Z,alpha,beta,gamma=tail(a,b,N,M)
    w=endpoint_threshold(alpha,beta,gamma)
    p=independent_counts(a,b,N,M,w)
    assert p[r]==A[0]*B[0]*w**r
    assert p[r-1]==A[1]*B[1]*w**r+X*w**(r-1)
    assert p[r-2]==A[2]*B[2]*w**r+Y*w**(r-1)+Z*w**(r-2)
    margin=(r-1)*p[r-1]**2-2*r*p[r-2]*p[r]
    assert margin==w**(2*r-2)*(alpha*w*w+beta*w+gamma)<0
    gg=gcd(gcd(abs(alpha),beta),gamma)
    rec={'a':a,'b':b,'rank':r,'t':t,'exterior_left':N,'exterior_right':M,
         'vertices':r+N+M,'edges':a*b+a*M+b*N,'core_activity':w,'exterior_activity':1,
         'primitive_endpoint_quadratic':[alpha//gg,beta//gg,gamma//gg],
         'exact_endpoint_margin':margin,'coefficients':p,
         'previous_integer_endpoint_quadratic_value':alpha*(w-1)**2+beta*(w-1)+gamma,
         'chosen_integer_endpoint_quadratic_value':alpha*w*w+beta*w+gamma}
    records.append(rec)
    print(json.dumps({k:rec[k]for k in('a','b','exterior_left','exterior_right','vertices','edges','core_activity','primitive_endpoint_quadratic')}),flush=True)
# Grid sanity checks of the clean universal populations and positivity assertions.
grid=0
for a in range(3,21):
    for b in range(3,21):
        r,K,H,t,N,M=parameters(a,b,universal=True)
        *_,alpha,beta,gamma=tail(a,b,N,M)
        assert alpha<0 and beta>0 and gamma>0
        endpoint_threshold(alpha,beta,gamma)
        grid+=1
report={'direct_endpoint_support_checks':len(records),'universal_population_grid_checks':grid,
        'scope':'Finite checks supplement the general proof; they are not its logical basis.',
        'records':records}
(Path(__file__).resolve().parents[1]/'data'/'negative_shapes_verification.json').write_text(json.dumps(report,indent=2)+'\n')
