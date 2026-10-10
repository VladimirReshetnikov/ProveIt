#!/usr/bin/env python3
"""Independent high-precision numerical diagnostics; NOT interval certificates.

The mathematical proof uses verify_exact.py, not decimal agreement here.
This file evaluates the defining Laplace integral, not a truncated Lerch sum.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import mpmath as mp

def F(a,mu,da=0,dmu=0):
    a=mp.mpf(a);mu=mp.mpf(mu)
    if not a>0 or mu<0:raise ValueError('a>0 and mu>=0 required')
    def integrand(x):
        if x==0:return mp.mpf('0')
        z=mp.log(x)+mp.euler
        q=z**3-3*mp.zeta(2)*z+2*mp.zeta(3)
        den=-mp.expm1(-x-mu)
        out=(-1)**da*x**(1+da)*mp.exp(-a*x)*q/den
        if dmu:out*=-mp.exp(-x-mu)/den
        return out
    pts=[mp.mpf('0')]
    if mu>0:pts+=[mu]
    pts += [mp.mpf('.001'),mp.mpf('.1'),1,10,mp.inf]
    pts=sorted(set(pts))
    return mp.quad(integrand,pts)

def order_jets(s0,rho,orders=(1,2,3),nodes=128):
    """Cauchy/Fourier differentiation, avoiding tiny real order increments.

    This is a numerical cross-check, not a certified quadrature rule.
    """
    R=mp.mpf('0.25')
    vals=[]
    for k in range(nodes):
        z=mp.exp(2j*mp.pi*(mp.mpf(k)+mp.mpf('0.5'))/nodes)
        vals.append((z,mp.polylog(mp.mpf(s0)+R*z,rho)))
    return {j:mp.re(mp.factorial(j)*sum(v*z**(-j) for z,v in vals)/(nodes*R**j)) for j in orders}

def run(dps=40):
    mp.mp.dps=dps
    ac,muc=mp.findroot(lambda a,u:(F(a,u),F(a,u,da=1)),
                      (mp.mpf('1.04975305'),mp.mpf('.00000953321')),
                      tol=mp.mpf(10)**(-dps+8),maxsteps=15)
    mustar=mp.findroot(lambda u:F(1,u),(mp.mpf('.000007'),mp.mpf('.000008')),
                       tol=mp.mpf(10)**(-dps+8),maxsteps=15)
    rhostar=mp.exp(-mustar);rhoc=mp.exp(-muc)
    astar=mp.findroot(lambda a:F(a,mustar),(mp.mpf('1.1'),mp.mpf('1.2')),
                     tol=mp.mpf(10)**(-dps+8))
    Fa=F(1,mustar,da=1);Frho=-F(1,mustar,dmu=1)/rhostar
    slope=-Frho/Fa
    span_second=6*slope*slope/Fa
    # Moment identity uses actual order derivatives of the polylogarithm,
    # independently of the defining Laplace representation.
    naive=mp.diff(lambda s:mp.polylog(s,rhostar),2,3)+3*mp.diff(lambda s:mp.polylog(s,rhostar),2,2)
    jets=order_jets(2,rhostar)
    L2,L3=jets[2],jets[3]
    j1,j3=order_jets(1,rhostar),order_jets(3,rhostar)
    C=j1[3]+3*j1[2]
    T=2*j3[3]+9*j3[2]+6*j3[1]
    poly_curvature=-6*C*C/(rhostar*T**3)
    sharp=[]
    for n in range(2,13):
        alpha=(3*n-mp.sqrt(n*n+8*n))/4
        R=lambda y:2*y*y-3*n*y+n*(n-1)+mp.exp(y-n)*y*(n-y)
        xi=mp.findroot(R,(alpha,mp.mpf(n-1)/2))
        sharp.append({'n':n,'alpha':str(alpha),'xi':str(xi),'exp_xi':str(mp.exp(xi))})
    return {'status':'NON-CERTIFIED numerical diagnostics','mpmath_dps':dps,
            'fold':{'a_c':str(ac),'mu_c':str(muc),'rho_c':str(rhoc),
                    'F_residual':str(F(ac,muc)),'Fa_residual':str(F(ac,muc,da=1))},
            'resonance':{'mu_star':str(mustar),'rho_star':str(rhostar),
                         'middle_zero':str(astar),'left_zero':'1 (exact by theorem)',
                         'outer_zero':'2 (exact by theorem)',
                         'common_drho_velocity':str(slope),'span_second_derivative':str(span_second),
                         'polylog_order_identity_residual':str(L3+3*L2),
                         'naive_finite_difference_residual':str(naive),
                         'polylog_curvature_identity_residual':str(poly_curvature-span_second),
                         'L2_order_derivative':str(L2)},
            'sharp_barriers':sharp}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dps',type=int,default=40)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'certificates'/'diagnostics.json')
    args=parser.parse_args()
    if args.dps<25:raise ValueError('use at least 25 decimal digits')
    d=run(args.dps);args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(d,indent=2)+'\n')
    print(json.dumps(d,indent=2))
if __name__=='__main__':main()
