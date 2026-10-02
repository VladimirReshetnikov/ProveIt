"""Exact partition-orientation coefficients by positive Kronecker encoding.

Use unsigned Touchard polynomials Q_k. Every coefficient of a product of
Q_{lambda_i} is bounded by Bell(n), hence every DP coefficient by p(n)Bell(n)
<= 2^n n^n. A base 2**bits above that bound prevents carries.
Recover AO by applying t^j -> (-1)^(n-j) j! after computing each coefficient.
"""
import sys, math, json, time
from pathlib import Path
import mpmath as mp

N = int(sys.argv[1]) if len(sys.argv)>1 else 150
bits = N*(1+math.ceil(math.log2(max(N,2))))+10
mask=(1<<bits)-1
row=[1]; Q=[1]
for k in range(1,N+1):
    row=[0]+[j*(row[j] if j<len(row) else 0)+row[j-1] for j in range(1,k+1)]
    Q.append(sum(v<<(bits*j) for j,v in enumerate(row)))
fac=[math.factorial(j) for j in range(N+1)]
out={"N":N,"bits":bits,"method":"positive Touchard Kronecker product"}
for distinct in [False,True]:
    start=time.time(); dp=[0]*(N+1); dp[0]=1
    for k in range(1,N+1):
        ran=range(N,k-1,-1) if distinct else range(k,N+1)
        for n in ran:dp[n]+=dp[n-k]*Q[k]
        if k%25==0:print(distinct,k,round(time.time()-start,2),flush=True)
    vals=[]
    for n,h in enumerate(dp):
        a=0
        for j in range(n+1):
            a+=((-1)**(n-j))*fac[j]*(h&mask);h>>=bits
        assert h==0 and a>0
        vals.append(str(a))
    out['distinct' if distinct else 'unrestricted']=vals
path=Path(__file__).with_name('exact_values_'+str(N)+'.json')
path.write_text(json.dumps(out,indent=2))
mp.mp.dps=50
for kind,C,A,pow_n in [('unrestricted','2.1587520056577855317373573144047825723165259312102','0.16481752396442050396187672134838365614759460482904',1),('distinct','0.90572982172019901788916250016056881567900117572326','0.21799921291820252233936031170847439858780754258368',mp.mpf('0.75'))]:
    print(kind)
    for n in [20,40,60,80,100,120,150,200,250,300,333,400]:
        if n>N:continue
        ratio=mp.mpf(out[kind][n])/mp.factorial(n)*n**pow_n*mp.exp(-mp.mpf(C)*mp.sqrt(n))/mp.mpf(A)
        print(n,mp.nstr(ratio,20),mp.nstr((ratio-1)*mp.sqrt(n),20))
