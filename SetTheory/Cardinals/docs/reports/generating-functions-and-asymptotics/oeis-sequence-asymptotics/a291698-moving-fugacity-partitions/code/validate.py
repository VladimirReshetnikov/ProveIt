"""Independent cross-checks and identity tests, not a substitute for proof."""
import json
from pathlib import Path
import mpmath as mp
from checks import *
mp.mp.dps=80
N=60;ps=exact_polynomials(list(range(1,N+1)))
for n in range(1,N+1):
    for alpha in (1,2):
        u=n**alpha
        coeffs=[0]*(n+1);coeffs[0]=1
        for k in range(1,n+1):
            for v in range(n,k-1,-1):coeffs[v]+=u*coeffs[v-k]
        assert coeffs[n]==exact_value(ps[n],u),(n,alpha)
known2=[1,1,4,90,272,1275,49284,124901,536640,1620648,104040100,223290012,880969104,2485978170,7454471332,592164776475,1138401673472,4109108002310,10877348160900,30962024560494,72270337440400,7523649856001916,13202150810778116,44577985082575400]
assert known2==[1]+[exact_value(ps[n],n*n) for n in range(1,24)]
identity=[]
for u,z in [(mp.mpf(20),mp.mpf('.1')),(mp.mpf(1000),mp.mpc('.08','.02')),(mp.mpf(20000),mp.mpc('.05','.095'))]:
    L=mp.log(u);q=mp.exp(-z);Q=mp.exp(-4*mp.pi**2/z)
    theta=sum((-1)**j*mp.exp((-2*mp.pi**2*j*j+2j*mp.pi*j*L)/z) for j in range(-30,31))
    rhs=u**(-mp.mpf('.5'))*mp.exp((L*L/2+mp.pi**2/6)/z+z/12)*theta/(mp.qp(Q,Q)*mp.qp(-1/u,q))
    lhs=mp.qp(-u*q,q)
    err=abs(rhs/lhs-1)
    assert err<mp.mpf('1e-65'),err
    identity.append({'u':str(u),'z':str(z),'relative_error':mp.nstr(err,10)})
rows=json.load(open(Path(__file__).with_name('checks.json')))['rows']
inv=[]
for alpha in [1,2]:
    row=next(r for r in rows if r['alpha']==str(alpha) and r['n']==20000)
    y=mp.mpf(row['log_exact'])
    for K in [0,1,2]:
        x=inverse(y,alpha,M=9,K=K)
        inv.append({'alpha':alpha,'n':20000,'M':9,'K':K,'inverse_minus_n':mp.nstr(x-20000,25)})
out={'independent_weighted_DP_checks':120,'OEIS_alpha2_terms_checked':24,'Jacobi_identity_checks':identity,'sector_inverse_checks':inv}
print(json.dumps(out,indent=2))
Path(__file__).with_name('validation.json').write_text(json.dumps(out,indent=2))
