import argparse
from pathlib import Path
_ap=argparse.ArgumentParser(description='Optional arbitrary-precision diagnostics; not interval certificates')
_ap.add_argument('--output-dir',required=True,type=Path,help='new output directory')
_output=_ap.parse_args().output_dir
_output.mkdir(exist_ok=False)
from functools import lru_cache
from math import factorial
from fractions import Fraction
import json
import mpmath as mp
@lru_cache(None)
def graph(r,u=-1):
    if not any(r):return 1
    i=next(k for k,t in enumerate(r) if t)
    q=list(r);q[i]-=1
    total=graph(tuple(q),i) if u in (-1,i) else 0
    for j,t in enumerate(q):
        if j!=i and t:
            qq=q.copy();qq[j]-=1
            total+=t*graph(tuple(qq),u)
    return total

def closed(n):
    terms=[divmod(factorial(2*n)*factorial(n)**2,factorial(2*j)*factorial(n-j)**2*factorial(j)) for j in range(n+1)]
    
    if not all(r==0 for t,r in terms):raise RuntimeError('nonintegral graph count')
    return sum(t for t,r in terms)
exact=[]
for n in range(16):
    r=graph((2*n,n,n));s=closed(n)
    if r!=s:raise RuntimeError('graph comparison differs')
    exact.append({'n':n,'graph':r,'sum':s})
print('Exact graph recursion vs factorial sum:',exact)
open(_output/'exact_counts.json','w').write(json.dumps(exact,indent=2))
mp.mp.dps=70
a=mp.power(4,-mp.mpf(1)/3)
c=[mp.mpf(1),211*a/216,172781*a*a/466560,-mp.mpf(189855337)/1209323520,-mp.mpf(6247138084769)*a/36569943244800]
logs=[None,211*a/216,-173*a*a/1620,-mp.mpf(55)/324,-389*a/122472]
def exact_dist(n):
    lo,hi=0,n
    while lo<hi:
        j=(lo+hi)//2
        if (n-j)**2>(2*j+2)*(2*j+1)*(j+1):lo=j+1
        else:hi=j
    mode=lo
    vals={mode:mp.mpf(1)}
    tail=mp.mpf(0)
    for k in range(mode,n):
        vals[k+1]=vals[k]*mp.mpf((n-k)**2)/((2*k+2)*(2*k+1)*(k+1))
        if vals[k+1]<mp.mpf('1e-80'):
            ratio=mp.mpf((n-k-1)**2)/((2*k+4)*(2*k+3)*(k+2)) if k+1<n else 0
            tail+=vals[k+1]*ratio/(1-ratio);break
    for k in range(mode,0,-1):
        vals[k-1]=vals[k]*mp.mpf(2*k*(2*k-1)*k)/(n-k+1)**2
        if vals[k-1]<mp.mpf('1e-80'):
            ratio=mp.mpf(2*(k-1)*(2*k-3)*(k-1))/(n-k+2)**2 if k>1 else 0
            tail+=vals[k-1]*ratio/(1-ratio);break
    Z=sum(vals.values());Ey=sum((j-mode)*w for j,w in vals.items())/Z
    mean=mode+Ey;var=sum((j-mode-Ey)**2*w for j,w in vals.items())/Z
    logt=2*mp.loggamma(n+1)-2*mp.loggamma(n-mode+1)-mp.loggamma(2*mode+1)-mp.loggamma(mode+1)
    return logt+mp.log(Z),mean,var,tail/Z,len(vals)
rows=[]
for n in [100,1000,10000,100000,1000000,10000000]:
    N=mp.root(n,3);q=1/N
    L=3*a*N*N-a*a*N+mp.mpf(1)/12-mp.log(12*mp.pi*a)/2-mp.log(N)
    exactlog,mean,var,tail,terms=exact_dist(n)
    R=mp.exp(exactlog-L)
    cs=[(R-sum(c[k]*q**k for k in range(r)))/q**r for r in range(1,5)]
    means=[(mean-a*N*N+2*a*a*N/3+mp.mpf(1)/12)/q,(mean-a*N*N+2*a*a*N/3+mp.mpf(1)/12-49*a*q/162)/q**2]
    variances=[var-a*N*N/3+4*a*a*N/9,(var-a*N*N/3+4*a*a*N/9-mp.mpf(1)/12)/q]
    row={'n':n,'coefficient_residuals':[mp.nstr(x,24) for x in cs],'mean_residuals':[mp.nstr(x,24) for x in means],'variance_residuals':[mp.nstr(x,24) for x in variances],'tail_relative_upper_bound':mp.nstr(tail,5),'terms':terms};rows.append(row);print(row)
print('Targets c1..c4:',[mp.nstr(x,24) for x in c[1:]])
print('Mean targets:',[mp.nstr(49*a/162,24),mp.nstr(-173*a*a/972,24)])
print('Variance targets:',[mp.nstr(mp.mpf(1)/12,24),mp.nstr(17*a/243,24)])
open(_output/'diagnostics.json','w').write(json.dumps(rows,indent=2))
