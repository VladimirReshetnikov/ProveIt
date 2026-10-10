#!/usr/bin/env python3
"""Independent floating-point diagnostics and rational bracket proposals.

This program does NOT certify a sign or an error bound. Run certify.py afterward.
Gauss--Laguerre quadrature is independent of the finite Euler sum.
"""
from __future__ import annotations
import json, math
from pathlib import Path
from fractions import Fraction as F
import numpy as np
import scipy
from scipy.special import roots_genlaguerre, gamma
from scipy.optimize import brentq
from certify import ROOT, coefficients, SCALE, euler_enclosure


def gaussian_quad(a: float,b: float,order: int=128) -> float:
    S,ws=roots_genlaguerre(order,a-1)
    T,wt=roots_genlaguerre(order,b-1)
    x=np.exp(-S[:,None]/2)
    y=x*np.exp(-T[None,:])
    kernel=(x+y)/((1+x*x)*(1+y*y))
    return -float(2**(-a)*np.sum(kernel*(ws/gamma(a))[:,None]*(wt/gamma(b))[None,:]))


def angle_root(a: F,b: F,rho: F):
    cc=coefficients(a,b,400)
    cf=np.array([(l+h)/(2*SCALE) for l,h in cc[1:]])
    r=float(rho)
    weighted=cf*r**np.arange(1,401)
    def fun(c):
        prev,cur=0.,1.
        total=0.
        for term in weighted:
            total+=term*cur
            prev,cur=cur,2*c*cur-prev
        return total
    return brentq(fun,r/2,r,xtol=5e-15)


def main():
    proposals=[]; root_summary=[]
    for aa,bb in [('1/10','1/10'),('1/4','1/4'),('2/5','1/5'),('1/3','1/3')]:
        etas=[]
        for rr in ['1/4','1/2','3/4']:
            c=angle_root(F(aa),F(bb),F(rr))
            B=10**12; k=math.floor(c*B)
            lo,hi=F(k-2,B),F(k+3,B)
            proposals.append({'a':aa,'b':bb,'rho':rr,'cosine_lower':str(lo),'cosine_upper':str(hi)})
            etas.append(c/float(F(rr)))
        root_summary.append({'a':aa,'b':bb,'eta_at_radii_1_4_1_2_3_4':etas})
    (ROOT/'data/angular_proposals.json').write_text(json.dumps(proposals,indent=2)+'\n')
    comparisons=[]
    for aa,bb in [('1/10','1/10'),('1/4','1/4'),('2/5','1/5'),('1/3','1/3'),
                  ('1/10','9/10'),('1/2','1/2'),('9/10','1/10'),('1','1'),('2','3')]:
        lo,hi=euler_enclosure(F(aa),F(bb))
        center=float((lo+hi)/2)
        q64=gaussian_quad(float(F(aa)),float(F(bb)),64)
        q128=gaussian_quad(float(F(aa)),float(F(bb)),128)
        comparisons.append({'a':aa,'b':bb,'euler_midpoint_approx':center,'quad_64':q64,
                            'quad_128':q128,'absolute_discrepancy_128':abs(q128-center)})
    monotonic=[]
    for w in [.4,.8,1.,1.5,3.,6.]:
        a_values=np.linspace(.1,.9,9)*w
        vals=[-gaussian_quad(float(a),float(w-a),96) for a in a_values]
        monotonic.append({'weight':w,'outer_orders':list(a_values),'negative_g':vals,
                          'strict_decrease_observed':all(vals[i]>vals[i+1] for i in range(8))})
    result={'status':'floating-point diagnostics, not certified quadrature',
            'numpy':np.__version__,'scipy':scipy.__version__,'quadrature_comparisons':comparisons,
            'angular_summaries':root_summary,'fixed_weight_grids':monotonic,
            'critical_constant_approx':math.pi/4+math.log(2)/2}
    (ROOT/'data/diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Maximum independent quadrature discrepancy:',max(x['absolute_discrepancy_128'] for x in comparisons))
    print('Fixed-weight monotonicity grids:',[x['strict_decrease_observed'] for x in monotonic])
    print('Angular summaries:',root_summary)

if __name__=='__main__':
    main()
