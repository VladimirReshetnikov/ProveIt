#!/usr/bin/env python3
"""High-precision numerical illustrations (mpmath required).

The 20-decimal interval for rho is certified separately by verify.py using
rational arithmetic. Other printed decimal constants are numerical estimates.
"""
from __future__ import annotations
import csv
import json
from pathlib import Path
import mpmath as mp
from verify import continued_fraction, multiply

ROOT=Path(__file__).resolve().parent

def connected(q: mp.mpf,depth: int=50) -> mp.mpf:
    c=mp.mpf(1)
    for j in range(depth,0,-1):
        v=q**j
        c=(1-v*c)/(1-v-v*c)
    return c-1


def main() -> None:
    mp.mp.dps=90
    rho=mp.findroot(lambda q:connected(q)-1,(mp.mpf('.31'),mp.mpf('.33')))
    p1=mp.diff(connected,rho)
    p2=mp.diff(connected,rho,2)
    kappa=1/(rho*p1)
    varcoef=kappa**2-kappa+p2/(rho*p1**3)
    # Independent depth check; this is a numerical stability test, not a certificate.
    assert abs(connected(rho,40)-connected(rho,60))<mp.mpf('1e-80')
    values={'rho':rho,'growth_constant':1/rho,'asymptotic_prefactor':kappa,
            'mean_components_per_cell':kappa,'variance_components_per_cell':varcoef,
            'Pprime_at_rho':p1,'Pdoubleprime_at_rho':p2}
    result={key:mp.nstr(v,65) for key,v in values.items()}
    result['precision_note']='Numerical estimates; only rho interval in verification_results.json is rationally certified.'
    result['mpmath_version']=mp.__version__
    (ROOT/'numerical_results.json').write_text(json.dumps(result,indent=2)+'\n')
    A,_=continued_fraction(1000)
    A2=multiply(A,A,1000)
    A3=multiply(A2,A,1000)
    with (ROOT/'asymptotic_checks.csv').open('w',newline='') as stream:
        writer=csv.writer(stream)
        writer.writerow(['n','a_n_times_rho_power_n','mean_components_over_n','variance_components_over_n'])
        for n in [10,20,50,100,250,500,1000]:
            mean=mp.mpf(A2[n]-A[n])/A[n]
            f2=mp.mpf(2*(A3[n]-2*A2[n]+A[n]))/A[n]
            var=f2+mean-mean**2
            writer.writerow([n,mp.nstr(A[n]*rho**n,35),mp.nstr(mean/n,35),mp.nstr(var/n,35)])
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
