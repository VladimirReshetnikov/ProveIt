"""Independent high-precision quadrature diagnostics (not interval proofs)."""
from pathlib import Path
from functools import lru_cache
import json
import mpmath as mp
from polylog_words import one_zero_formula, two_zero_height_one

ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=75

@lru_cache(None)
def li_series(indices, z):
    if not indices:return mp.mpf(1)
    r=abs(z)
    if r>=1:raise ValueError('This evaluator requires |z|<1.')
    N=int(mp.ceil((mp.mp.dps+25)*mp.log(10)/(-mp.log(r))))+30
    d=len(indices);h=[mp.mpf(0)]*(d+1);h[d]=mp.mpf(1)
    total=mp.mpc(0);zn=mp.mpc(1)
    for n in range(1,N+1):
        zn*=z
        total+=zn*h[1]/mp.mpf(n)**indices[0]
        for j in range(1,d):
            h[j]+=h[j+1]/mp.mpf(n)**indices[j]
    return total

def mzv(S):
    if not S:return mp.mpf(1)
    if len(S)==1:return mp.zeta(S[0])
    if len(S)==2 and S[1]==1:
        n=S[0]
        return n*mp.zeta(n+1)/2-mp.fsum(mp.zeta(n-j)*mp.zeta(j+1) for j in range(1,n-1))/2
    raise ValueError(f'Unsupported MZV for this diagnostic: {S}')

def value(red,z):
    q=1/(1-z);L=mp.log(q)
    return mp.fsum(mp.mpf(c.numerator)/c.denominator*L**j*li_series(S,q)*mzv(T)
                   for (j,S,T),c in red.items())

def main():
    cases=[]
    points=[('negative rational',-mp.mpf(1)/2),('Gaussian',mp.j),
            ('Eisenstein',-mp.mpf(1)/2+mp.j*mp.sqrt(3)/2)]
    for name,z in points:
        L=-mp.log(1-z)
        for weight in range(2,11):
            for a in range(weight-1):
                b=weight-2-a
                def integrand(t):
                    if t==0:return 0
                    v=-mp.log(1-z*t)
                    return (L-v)**a*v**(b+1)/t
                direct=mp.quad(integrand,[0,mp.mpf('.25'),1])/(mp.factorial(a)*mp.factorial(b+1))
                derived=value(one_zero_formula(a,b),z)
                err=abs(direct-derived)
                assert err<mp.mpf('1e-65'),(name,a,b,err)
                cases.append(dict(family='one-zero',point=name,weight=weight,a=a,b=b,
                                  absolute_residual=mp.nstr(err,12)))
        for weight in range(3,9):
            b=weight-3
            def integrand(t):
                if t==0:return 0
                return -mp.log(t)*(-mp.log(1-z*t))**(b+1)/t
            direct=mp.quad(integrand,[0,mp.mpf('.25'),1])/mp.factorial(b+1)
            derived=value(two_zero_height_one(weight),z)
            err=abs(direct-derived)
            assert err<mp.mpf('1e-65'),(name,weight,err)
            cases.append(dict(family='two-zero-height-one',point=name,weight=weight,
                              absolute_residual=mp.nstr(err,12)))
    worst=max(mp.mpf(c['absolute_residual']) for c in cases)
    report=dict(status='PASS',precision_decimal_digits=mp.mp.dps,cases=len(cases),
                maximum_absolute_residual=mp.nstr(worst,15),
                qualification='Independent quadrature diagnostics; not directed-rounding certificates.',
                details=cases)
    (ROOT/'certificates'/'numerical_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print({k:v for k,v in report.items() if k!='details'})

if __name__=='__main__':main()
