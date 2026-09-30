#!/usr/bin/env python3
"""Independent finite-quadrature checks of contour signs and exact identities.
No rigorous quadrature or branch-domain certification is claimed.
"""
from __future__ import annotations
import json
from pathlib import Path
import mpmath as mp
from verify import inverse, mp_coefficients, ROOT

mp.mp.dps=100
R=mp.mpf(2)
X=mp.mpf(5)
M=15
_,h=mp_coefficients(M)
true=inverse(X)-X-mp.fsum(h[j]*X**(1-2*j) for j in range(1,M+1))

def gauss(f,a,b,nodes,weights):
    center=(a+b)/2; half=(b-a)/2
    return half*mp.fsum(weights[j]*f(center+half*nodes[j]) for j in range(len(nodes)))

rows=[]
for n in (20,36):
    nodes,weights=mp.gauss_quadrature(n,'legendre')
    def kernel(theta):
        z=R*mp.exp(mp.j*theta)
        return (inverse(z)-z)*z**(2*M+1)/(1-(z/X)**2)
    arc=gauss(kernel,mp.mpf(0),mp.pi/2,nodes,weights)
    core=2*mp.re(arc)/(mp.pi*X**(2*M+1))
    def spectral(t):
        rho=-mp.re(inverse(mp.j*t))
        return rho*t**(2*M)/(1+(t/X)**2)
    intervals=[mp.mpf(v) for v in (2,3,5,8,12,20)]
    integral=mp.fsum(gauss(spectral,a,b,nodes,weights)
                         for a,b in zip(intervals,intervals[1:]))
    moment=2*(-1)**(M+1)*integral/(mp.pi*X**(2*M+1))
    error=core+moment-true
    row={k:mp.nstr(v,45) for k,v in {'core_tail':core,'spectral_tail':moment,
              'direct_remainder':true,'identity_difference':error,
              'relative_difference':error/true}.items()}
    row['nodes_per_interval']=n
    rows.append(row)
    print(json.dumps(row,indent=2),flush=True)
# ed. (2026-09-29): LF line endings on every platform, like the filed files.
(ROOT/'data'/'contour_check.json').write_text(newline='\n',data=json.dumps({
    'precision':mp.mp.dps,'R':str(R),'X':str(X),'M':M,
    'spectral_integral_upper_cutoff':20,'tests':rows,
    'status':'Finite floating-point quadrature tests, not certified error bounds.'},indent=2)+'\n')
assert abs(mp.mpf(rows[-1]['relative_difference']))<mp.mpf('1e-12')
