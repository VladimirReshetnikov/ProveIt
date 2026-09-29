#!/usr/bin/env python3
"""Independent endpoint check by subtracting the finite Stirling expansion.

Precision grows with x to retain the exponentially small difference. This is
high-precision floating point, not interval arithmetic.
"""
from pathlib import Path
import csv
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
rows=[]
for xi in [10,30,60]:
    mp.mp.dps=5*xi+100
    x=mp.mpf(xi); b=2*mp.pi
    K0=int(mp.nint((b*x+mp.mpf('.5'))/2))
    exact=mp.loggamma(2*x+1)-2*mp.loggamma(x+1)
    core=2*x*mp.log(2)-mp.log(mp.pi*x)/2
    choices={}
    for K in [K0-1,K0,K0+1]:
        value=core+sum(mp.bernoulli(2*k)/(2*k*(2*k-1))
            *(mp.mpf(2)**(1-2*k)-2)/x**(2*k-1) for k in range(1,K+1))
        signed=exact-value
        assert (-1)**(K+1)*signed>0
        choices[K]=abs(signed)
    K=min(choices,key=choices.get)
    assert K==K0
    normalized=choices[K]*mp.exp(b*x)*b*mp.sqrt(x)/2
    dz=abs(2*K-(b*x+mp.mpf('.5')))
    predicted=1+(dz*dz/2-mp.mpf(13)/24)/(b*x)
    rows.append({'z':xi,'K_opt':K,'normalized_remainder':mp.nstr(normalized,24),
                 'second_order_prediction':mp.nstr(predicted,24),
                 'difference_times_z_squared':mp.nstr((normalized-predicted)*x*x,16),
                 'working_digits':mp.mp.dps})
with (ROOT/'data'/'endpoint_independent.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
print(rows)
