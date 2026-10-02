#!/usr/bin/env python3
"""Independent continuum quadrature checks of the log-expansion coefficients.
These check analytic coefficients, not integer coefficients at the huge implied n.
"""
from pathlib import Path
import csv
import mpmath as mp
from verify import log_approx
mp.mp.dps=70

def evaluate(alpha,s):
    M=mp.exp(s)
    def ep(u):
        if not u:return -mp.inf
        return alpha*(s*(1-u)+mp.log(u))
    # Integrate around the transition; endpoint errors are retained by quadrature.
    h=1/(alpha*(s-1))
    cuts=sorted(set([mp.mpf(0),mp.exp(-s),1/s,mp.mpf('.5'),
                     max(mp.mpf('.5'),1-8*h),mp.mpf(1),1+8*h,mp.mpf(2),mp.inf]))
    I=mp.quad(lambda u:mp.log1p(mp.exp(ep(u))),cuts)
    V=mp.quad(lambda u:u/(1+mp.exp(-ep(u))) if u else 0,cuts)
    n=M*M*V; K=mp.sqrt(2*n); r=mp.log(K)
    entropy=M*I+n*alpha*s/M
    c=mp.pi**2/(6*alpha**2)
    P8=c+mp.mpf(259)/2*c*c+mp.mpf(7271)/10*c**3+mp.mpf(157813)/840*c**4
    residual=(entropy-log_approx(alpha,n,7))/(alpha*K)*r**8
    return {'alpha':alpha,'s':s,'r':mp.nstr(r,18),
            'scaled_remainder_after_P7':mp.nstr(residual,24),
            'predicted_limit_P8':mp.nstr(P8,24)}
if __name__=='__main__':
    rows=[]
    for alpha in (1,3):
        for s in (12,24,48,96):
            row=evaluate(alpha,mp.mpf(s));rows.append(row);print(row,flush=True)
    p=Path(__file__).resolve().parent/'data'/'continuum_diagnostics.csv'
    with p.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
