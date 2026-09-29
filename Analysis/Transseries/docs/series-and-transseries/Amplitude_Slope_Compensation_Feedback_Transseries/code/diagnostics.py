#!/usr/bin/env python3
"""Floating-point large-order diagnostics, explicitly not certificates."""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
import numpy as np
from scipy.special import logsumexp, gammaln
from fractions import Fraction as F
from verify import coefficients


def logarithmic_coefficients(N: int, p: float, beta: float, b: float) -> np.ndarray:
    if N < 1 or p <= 0 or beta <= 0 or b <= 0:
        raise ValueError('N, p, beta, and b must be positive.')
    indices = np.arange(N+1,dtype=float)
    logc = -b*indices**beta
    logc[1] = 0.
    loglam = np.full(N+1,-np.inf)
    loglam[1:] = p*np.log(indices[1:])
    u = np.full(N+1,-np.inf)
    E = np.full((N+1,N+1),-np.inf)
    E[1:,0] = 0.
    lm = np.zeros(N+1)
    lm[1:] = np.log(indices[1:])
    for n in range(1,N+1):
        for j in range(1,n):
            k = n-j
            E[j,k] = loglam[j]-math.log(k)+logsumexp(lm[1:k+1]+u[1:k+1]+E[j,k-1::-1])
        js = np.arange(1,n+1)
        u[n] = logsumexp(logc[js]+E[js,n-js])
    return u


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--order',type=int,default=512)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'diagnostics.json')
    args = parser.parse_args()
    if not 20 <= args.order <= 2000:
        parser.error('--order must be between 20 and 2000.')
    b = math.log(2.)
    rows = []
    max_diff = 0.
    for p in (3,4,5):
        logs = logarithmic_coefficients(args.order,p,2,b)
        c=[F(0),F(1)]+[F(1,2**(j*j)) for j in range(2,21)]
        lam=[F(0)]+[F(j**p) for j in range(1,21)]
        exact=coefficients(c,lam,20)
        for n in range(1,21):
            lexact=math.log(exact[n].numerator)-math.log(exact[n].denominator)
            max_diff=max(max_diff,abs(logs[n]-lexact))
        r=p/2
        s=r-1
        T=(r/b)**r
        for n in (64,128,256,512):
            if n<=args.order:
                root=math.exp((logs[n]-s*gammaln(n+1))/n)
                rows.append({'p':p,'beta':2,'b':b,'n':n,'gevrey_order':s,
                             'type_limit':T,'type_root':root,'root_over_limit':root/T,
                             'log_forward_coefficient':float(logs[n])})
    assert max_diff<2e-10
    lower_rows=[]
    for p in (3,4,5):
        r=p/2;s=r-1;T=(r/b)**r
        for n in (10**3,10**4,10**5,10**6):
            j0=math.sqrt(r*n/b)
            best=(-math.inf,0)
            for j in range(max(2,int(j0)-8), min(n,int(j0)+8)+1):
                m=n-j
                ll=-b*j*j+m*math.log(j**p+m)-math.lgamma(m+1)
                if ll>best[0]:best=(ll,j)
            lower_rows.append({'p':p,'n':n,'action_index':best[1],
                               'lower_type_root_over_limit':math.exp((best[0]-s*math.lgamma(n+1))/n)/T})
    result={'label':'Floating diagnostics, not interval certificates',
            'recurrence_checked_against_exact_through':20,'max_log_discrepancy':max_diff,
            'full_coefficient_rows':rows,'one_large_action_lower_bound_rows':lower_rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    for row in rows:
        print(f"p={row['p']} n={row['n']:4d} type root/T={row['root_over_limit']:.9f}")
    print('Maximum log error versus exact:',max_diff)

if __name__=='__main__':main()
