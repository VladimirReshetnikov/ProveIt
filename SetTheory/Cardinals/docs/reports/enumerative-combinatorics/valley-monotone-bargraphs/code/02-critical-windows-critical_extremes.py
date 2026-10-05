#!/usr/bin/env python3
"""Numerical tests of mixed critical extremes and a two-level critical window.
These are finite diagnostics, not rigorous error certificates.
"""
from __future__ import annotations
import json
from pathlib import Path
import mpmath as mp
from verify import coefficients
from numerics import K, root, moment

mp.mp.dps=60
OUT=Path(__file__).resolve().parent.parent/'data'


def scaled_level(N,j,q,u,unext,dnext):
    """D_j coefficients in the variable q*z; dnext is already scaled."""
    ks=[mp.mpf(0)]*(N+1); bs=ks[:]
    for n in range(N+1):
        ks[n]=mp.fsum(mp.mpf(unext[n-r])*q**n for r in range(j,n+1,j))
        bs[n]=mp.fsum((r//j+1)*q**r*dnext[n-r] for r in range(0,n+1,j))
    f=[mp.mpf(0)]*(N+1)
    for n in range(N+1):
        f[n]=bs[n]+u*mp.fsum(ks[k]*f[n-k] for k in range(2*j+1,n+1))
    for n in range(j,N+1,j):f[n]+=q**n
    return f


def run():
    data=json.loads((OUT/'numerical_checks.json').read_text())
    c={k:mp.mpf(v) for k,v in data['constants'].items()}
    R,uc=c['R'],c['uc'];a1,a0=c['critical_height_alpha1'],c['critical_height_alpha2']
    N=240
    _,_,levels=coefficients(N,retain=True)
    f=scaled_level(N,1,R,uc,levels[2][0],
                   [mp.mpf(x)*R**n for n,x in enumerate(levels[2][1])])
    mixed=[]
    for n in [120,240]:
        for h in ([7,8,9] if n==120 else [9,10,11]):
            _,_,lev=coefficients(n,cap=h,retain=True)
            fh=scaled_level(n,1,R,uc,lev[2][0],
                  [mp.mpf(x)*R**k for k,x in enumerate(lev[2][1])])
            tau=n*R**h
            pred=(mp.exp(-tau*a1)-mp.exp(-tau*a0))/(tau*(a0-a1))
            mixed.append({'n':n,'h':h,'exact_cdf':mp.nstr(fh[n]/f[n],30),
                          'mixture_prediction':mp.nstr(pred,30)})
    R3=root(3)
    u1,u2=1/K(R3,1),1/K(R3,2)
    M1,M2=moment(R3,1)[0],moment(R3,2)[0]
    def multi(s1,s2):
        d3=[mp.mpf(x)*R3**k for k,x in enumerate(levels[3][1])]
        d2=scaled_level(N,2,R3,u2*mp.exp(mp.mpf(s2)/N),levels[3][0],d3)
        return scaled_level(N,1,R3,u1*mp.exp(mp.mpf(s1)/N),levels[2][0],d2)[N]
    base=multi(0,0); multirows=[]
    for s1,s2 in [(3,-2),(-3,2)]:
        points=[mp.mpf(0),mp.mpf(s1)/M1,mp.mpf(s2)/M2]
        integral=2*mp.fsum(mp.exp(x)/mp.fprod(x-y for j,y in enumerate(points) if j!=i)
                           for i,x in enumerate(points))
        multirows.append({'n':N,'s1':s1,'s2':s2,'exact_ratio':mp.nstr(multi(s1,s2)/base,30),
                           'simplex_prediction':mp.nstr(integral,30)})
    result={'status':'completed numerical diagnostics',
            'warning':'No rigorous interval enclosure is claimed.',
            'critical_height_checks':mixed,
            'two_level_constants':{k:mp.nstr(v,30) for k,v in
                   dict(R3=R3,u1=u1,u2=u2,M1=M1,M2=M2).items()},
            'two_level_window_checks':multirows}
    (OUT/'critical_extreme_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':run()
