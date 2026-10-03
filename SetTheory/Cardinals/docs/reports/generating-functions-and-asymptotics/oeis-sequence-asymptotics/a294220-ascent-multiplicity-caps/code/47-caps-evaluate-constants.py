#!/usr/bin/env python3
"""High-precision values of the proved bounded-multiplicity root constants."""
import json
import mpmath as mp
mp.mp.dps=70
out={}
for b in range(2,11):
    def integrand(v):
        if not v: return mp.mpf(1)
        term=mp.mpf(1); E=term
        for j in range(1,b+1):
            term*=v/j; E+=term
        return mp.log(E)/(E-1)
    T=mp.quad(integrand,[0,1,4,16,mp.inf])
    out[str(b)]={"T_b":mp.nstr(T,55),"mu_b":mp.nstr(1/T,55)}
assert abs(mp.mpf(out['2']['T_b'])-3*mp.pi**2/8)<mp.mpf('1e-53')
out['infinity']={"T_b":mp.nstr(mp.pi**2/6,55),"mu_b":mp.nstr(6/mp.pi**2,55)}
print(json.dumps(out,indent=2))
