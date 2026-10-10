#!/usr/bin/env python3
"""Exact symbolic coefficients and numerical diagnostics for joint log-gamma moments.

The analytic error bounds are proved in the article. Numerical quadrature here is
corroboration, not an interval certificate or a proof of an asymptotic theorem.
"""
from __future__ import annotations

import argparse
import json
import platform
from pathlib import Path

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]


def symbolic_coefficients():
    """Derive C1 and C2 independently from the gamma cumulant operator."""
    v, t, lam = sp.symbols("v t lambda", positive=True)
    a, a2, a3, b, d, e = sp.symbols("a a2 a3 b d e")
    A = lam * sp.exp(-v) * (b + a*t/(t+v))
    B = (a*lam*sp.exp(-v)*t/(t+v)
         + lam**2*sp.exp(-2*v)*(d+a2*t/(t+v)-a*a*t/(2*(t+v)**2)))
    C = (lam**2*sp.exp(-2*v)*t*(a2/(t+v)-a*a/(2*(t+v)**2))
         + lam**3*sp.exp(-3*v)*(e+t*(a3/(t+v)
             -a*a2/(t+v)**2+a**3/(3*(t+v)**3))))
    az = [sp.diff(A,v,j).subs(v,0) for j in range(5)]
    bz = [sp.diff(B,v,j).subs(v,0) for j in range(3)]
    r2 = az[2]+az[1]**2
    r3 = az[3]+3*az[1]*az[2]+az[1]**3
    r4 = az[4]+4*az[1]*az[3]+3*az[2]**2+6*az[1]**2*az[2]+az[1]**4
    c1 = sp.expand(bz[0]+az[1]+t*r2/2)
    c2 = sp.expand(C.subs(v,0)+bz[0]**2/2+bz[1]+az[1]*bz[0]
                   +t*(bz[2]+2*az[1]*bz[1]+r2*bz[0])/2
                   -az[1]+(2-t)*r2/2+5*t*r3/6+t*t*r4/8)
    g,z2,z3,z4 = sp.symbols("gamma Z2 Z3 Z4", nonzero=True)
    substitution = {a:-g,a2:z2/2,a3:-z3/3,b:z2/(2*g),
                    d:z3/(3*g)-z2*z2/(8*g*g),
                    e:z4/(4*g)-z2*z3/(6*g*g)+z2**3/(24*g**3)}
    c1 = sp.factor(c1.subs(substitution))
    c2 = sp.collect(sp.expand(c2.subs(substitution)),lam)
    c = z2/(2*g)-g
    target = lam*(c*(t/2-1)-2*g)+lam**2*(c*c*t/2+g*g+z3/(3*g)-z2*z2/(8*g*g))
    assert sp.cancel(c1-target)==0
    assert sp.Poly(c1,t,lam).degree(t)<=1
    assert sp.Poly(c2,t,lam).degree(t)<=2
    # Exact gamma moments around the mode, independently from the MGF.
    r=sp.symbols("r",positive=True)
    expected=[1/r,t/r+2/r**2,5*t/r**2+6/r**3,
              3*t*t/r**2+26*t/r**3+24/r**4]
    for j,target_moment in enumerate(expected,1):
        moment=sp.Add(*(sp.binomial(j,k)*(-t)**(j-k)*sp.rf(r*t+1,k)/r**k
                        for k in range(j+1)))
        assert sp.expand(moment-target_moment)==0
    return {"symbols":(t,lam,g,z2,z3,z4),"C1":c1,"C2":c2}


def loggamma_pair(x):
    """Stable log Gamma(1+x), log Gamma(1-x), including tiny positive x."""
    if x<mp.mpf("0.1"):
        plus=-mp.euler*x
        minus=mp.euler*x
        p=x*x
        j=2
        while True:
            term=mp.zeta(j)*p/j
            plus+=(-1)**j*term
            minus+=term
            if abs(term)<mp.eps*abs(minus)/8:
                return plus,minus
            p*=x
            j+=1
    return mp.loggamma(1+x),mp.loggamma(1-x)


def ratio_y(n,m):
    """Full transformed integral, split around the gamma mode."""
    r=m+1
    t=mp.mpf(n)/r
    sd=mp.sqrt(n+1)/r
    norm=(n+1)*mp.log(r)-mp.loggamma(n+1)-m*mp.log(mp.euler)
    def integrand(y):
        if y<=0 or mp.isinf(y):
            return mp.mpf(0)
        x=mp.exp(-y)
        if x>=1:
            return mp.mpf(0)
        ell,B=loggamma_pair(x)
        f=y+ell if x<mp.mpf("0.1") else mp.loggamma(x)
        if f<=0 or B<=0:
            return mp.mpf(0)
        return mp.exp(n*mp.log(f)+m*mp.log(B)-y+norm)
    knots=[mp.mpf(0)]+[t+k*sd for k in (-16,-8,-4,0,4,8,16) if t+k*sd>0]+[mp.inf]
    return mp.quad(integrand,knots)


def ratio_x(n,m):
    """Independent direct x integral, with knots at the transformed saddle."""
    t=mp.mpf(n)/(m+1)
    x0=mp.exp(-t)
    sd=mp.sqrt(n+1)/(m+1)
    norm=(n+1)*mp.log(m+1)-mp.loggamma(n+1)-m*mp.log(mp.euler)
    def integrand(x):
        if x<=0 or x>=1:
            return mp.mpf(0)
        f=mp.loggamma(x)
        B=loggamma_pair(x)[1]
        if f<=0 or B<=0:
            return mp.mpf(0)
        return mp.exp(n*mp.log(f)+m*mp.log(B)+norm)
    knots=sorted(set([mp.mpf(0),mp.mpf(1)]+
        [x0*mp.exp(k*sd) for k in (-16,-8,-4,0,4,8,16)
         if 0<x0*mp.exp(k*sd)<1]))
    return mp.quad(integrand,knots)


def make_report(dps=60,quick=False):
    coeff=symbolic_coefficients()
    ROOT.joinpath("data").mkdir(exist_ok=True)
    symbolic={"C1":str(coeff["C1"]),"C2":str(coeff["C2"]),
              "C1_tex":sp.latex(coeff["C1"]),"C2_tex":sp.latex(coeff["C2"]),
              "status":"exact symbolic equalities; not numerical period identities"}
    (ROOT/"data/moment_symbolic.json").write_text(json.dumps(symbolic,indent=2)+"\n")
    f2=sp.lambdify(coeff["symbols"],coeff["C2"],"mpmath")
    cases=[(30,0),(100,0),(300,0),(1000,0),(100,1),(100,-1),(1000,1),(1000,-1)]
    if quick:
        cases=[(30,0),(100,0)]
    rows=[]
    mp.mp.dps=dps
    g=mp.euler;c=mp.zeta(2)/(2*g)-g
    d=mp.zeta(3)/(3*g)-mp.zeta(2)**2/(8*g*g)
    for m,s in cases:
        n=int(mp.nint((m+1)*(mp.log(m)+s)))
        t=mp.mpf(n)/(m+1);lam=m*mp.exp(-t)
        yvalue=ratio_y(n,m)
        xvalue=ratio_x(n,m)
        lead=mp.exp(c*lam)
        c1=lam*(c*(t/2-1)-2*g)+lam*lam*(c*c*t/2+g*g+d)
        c2=f2(t,lam,g,mp.zeta(2),mp.zeta(3),mp.zeta(4))
        one=lead*(1+c1/m);two=lead*(1+c1/m+c2/m**2)
        difference=abs(xvalue-yvalue)
        assert difference < mp.power(10,-min(35,dps//2))*max(1,abs(yvalue))
        row={"m":m,"n":n,"s_target":s,"t":mp.nstr(t,dps),
             "lambda":mp.nstr(lam,dps),"ratio_y":mp.nstr(yvalue,dps),
             "ratio_x":mp.nstr(xvalue,dps),"engine_difference":mp.nstr(difference,10),
             "leading":mp.nstr(lead,dps),"one_correction":mp.nstr(one,dps),
             "two_corrections":mp.nstr(two,dps),
             "error_one":mp.nstr(yvalue-one,dps),"error_two":mp.nstr(yvalue-two,dps)}
        rows.append(row)
        print(json.dumps({k:row[k] for k in ("m","n","engine_difference","error_one","error_two")}),flush=True)
    report={"status":"numerical corroboration; quadrature is not interval-certified",
            "dps":dps,"python":platform.python_version(),"mpmath":mp.__version__,
            "sympy":sp.__version__,"rows":rows}
    (ROOT/"data/moment_numerics.json").write_text(json.dumps(report,indent=2)+"\n")
    return report


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--dps",type=int,default=60)
    parser.add_argument("--quick",action="store_true")
    args=parser.parse_args()
    make_report(args.dps,args.quick)
