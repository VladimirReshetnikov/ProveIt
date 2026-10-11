#!/usr/bin/env python3
"""Exact and high-precision diagnostic replay for higher_resonance_notes.tex.

The arbitrary-parameter claims are proved in the notes.  This script supplies
independent finite arithmetic checks and numerical diagnostics, not a proof
by matching decimal values.  Requires sympy and mpmath.
"""
from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp
import sympy as sp

mp.mp.dps = 65
OUT = (Path(__file__).resolve().parent.parent / 'data').joinpath("higher_resonance_checks.json")


def textnum(v):
    if isinstance(v, (mp.mpc, complex)):
        return {"re": mp.nstr(mp.re(v), 35), "im": mp.nstr(mp.im(v), 35)}
    return mp.nstr(v, 35)


def exact_checks():
    H, x = sp.symbols("H x")
    M0 = x / (x + 1)
    M1 = H + 2 / (x + 1) - 2
    M2 = x - 3 * H - 4 / (x + 1) + 4
    S = x - H**2 + H - 1 - (H - 1) / (x + 1)
    K = 1 - H / x - (H - 1) / (x + 1)
    assert sp.cancel(M0 * M2 - M1**2 - S) == 0
    assert sp.cancel(S - S.subs({x: x - 1, H: H - 1/x}, simultaneous=True) - K) == 0
    for N in range(16):
        direct = sp.Add(*[
            sp.Rational((n-m)**2, (m+1)*(m+2)*(n+1)*(n+2))
            for m in range(N+1) for n in range(m+1, N+1)
        ])
        closed = S.subs({x: N+1, H: sp.harmonic(N+1)})
        assert sp.cancel(direct - closed) == 0
    z = sp.symbols("z")
    # Build the polynomial series from independent elementary functions.
    log_series = -sum(z**j/sp.Integer(j) for j in range(1, 33))
    li2_series = sum(z**j/sp.Integer(j*j) for j in range(1, 32))
    G = z/(1-z)-1-li2_series-(1+z)/(2*z)*log_series**2-log_series/z
    expanded = sp.series(G, z, 0, 30).removeO().expand()
    for m in range(1, 30):
        assert sp.cancel(expanded.coeff(z, m) - K.subs({x:m,H:sp.harmonic(m)})) == 0
    a,c,u = sp.symbols("a c u")
    t=a*c+a+c
    assert sp.expand(u*(u+t)-a*c*(u-1)-(u+a)*(u+c)) == 0
    return {"status":"pass", "finite_cutoffs":16, "generator_coefficients":29,
            "symbolic_identities":3}


def cutoff_case(a,c, Ns=(1000,5000,20000)):
    b=a+c+1
    w=mp.gamma(a)*mp.gamma(c)/mp.gamma(b)
    A=1/(a*c)
    h=1+1/a+1/c
    B=-mp.euler-mp.digamma(a+1)-mp.digamma(c+1)
    m0=m1=m2=mp.mpf(0)
    rows=[]
    for n in range(max(Ns)+1):
        m0 += w
        m1 += n*w
        m2 += n*n*w
        if n in Ns:
            x=mp.mpf(n+1)
            actual=m0*m2-m1*m1
            model=A*x-(mp.log(x)+B)**2-h*(mp.log(x)+B)-2-A
            err=actual-model
            # The theorem predicts an error O(log^2 x/x); this reports
            # the observed error without pretending to certify its constant.
            rows.append({"N":n,"cutoff":textnum(actual),"model":textnum(model),
                         "residual":textnum(err),
                         "scaled_absolute_residual":textnum(abs(err)*x/mp.log(x)**2)})
        w *= (n+a)*(n+c)/((n+b)*(n+1))
    assert abs(rows and (actual-model)) < mp.mpf("0.02")
    return {"a":textnum(a),"c":textnum(c),"rows":rows}


def Gvalue(z):
    if z == 0:
        return mp.mpf(0)
    if z < mp.mpf("0.01"):
        H=mp.mpf(0)
        out=mp.mpf(0)
        power=mp.mpf(1)
        for m in range(1,42):
            H+=mp.mpf(1)/m
            power*=z
            out+=power*(1-H/m-(H-1)/(m+1))
        return out
    log=mp.log1p(-z)
    return z/(1-z)-1-mp.polylog(2,z)-(1+z)/(2*z)*log**2-log/z


def endpoint_checks():
    values={
      2:3*mp.zeta(2)-2*mp.zeta(3)-mp.mpf(5)/4*mp.zeta(4)-1,
      3:1-2*mp.zeta(2)+4*mp.zeta(3)-mp.mpf(5)/4*mp.zeta(4)
        -3*mp.zeta(5)+mp.zeta(2)*mp.zeta(3),
    }
    rows=[]
    for q,rhs in values.items():
        def integrand(z):
            if z==0:
                return mp.mpf(0)
            if z==1:
                return mp.mpf(1) if q==2 else mp.mpf(0)
            return (-mp.log(z))**(q-1)*Gvalue(z)/(z*mp.factorial(q-1))
        quadrature=mp.quad(integrand,[0,mp.mpf(".01"),mp.mpf(".1"),mp.mpf(".5"),mp.mpf(".9"),1])
        residual=quadrature-rhs
        assert abs(residual)<mp.mpf("1e-45")
        rows.append({"q":q,"value":textnum(rhs),"quadrature_residual":textnum(residual)})
    half=Gvalue(mp.mpf(1)/2)
    half_rhs=2*mp.log(2)-mp.log(2)**2-mp.pi**2/12
    assert abs(half-half_rhs)<mp.mpf("1e-60")
    return {"endpoint_integrals":rows,"half_argument":textnum(half),
            "half_residual":textnum(half-half_rhs)}


def laurent_check(a,c):
    A=1/(a*c)
    h=1+1/a+1/c
    B=-mp.euler-mp.digamma(a+1)-mp.digamma(c+1)
    T=mp.zeta(2)-mp.polygamma(1,a+1)-mp.polygamma(1,c+1)
    const=-(2*B**2+T+2*h*B+h+A)
    rows=[]
    for u in [mp.mpf("1e-4"),mp.mpf("1e-6"),mp.mpf("1e-8")]:
        L=mp.gamma(a+1)*mp.gamma(c+1)*mp.gamma(1+u)/(mp.gamma(a+1+u)*mp.gamma(c+1+u))
        exact=-L**2*(1+u/a)*(1+u/c)/(u**2*(1-u))
        remainder=exact+1/u**2+(2*B+h)/u-const
        assert abs(remainder)<100*abs(u)
        rows.append({"u":textnum(u),"post_constant_remainder":textnum(remainder),
                     "remainder_over_u":textnum(remainder/u)})
    return {"a":textnum(a),"c":textnum(c),"spectral_constant":textnum(const),"rows":rows}


def stieltjes_jet_checks():
    a,c,alpha=mp.mpf(3)/5,mp.mpf(7)/4,mp.mpf(2)/3
    b=a+c+1
    t=a*c+a+c
    B=-mp.euler-mp.digamma(a+1)-mp.digamma(c+1)
    T=mp.zeta(2)-mp.polygamma(1,a+1)-mp.polygamma(1,c+1)
    rhs0=B+mp.digamma(alpha)
    rhs1=(B*B+T)/2+mp.stieltjes(1,alpha)
    w=mp.gamma(a)*mp.gamma(c)/mp.gamma(b)
    psi=mp.digamma(b)
    s0=s1=mp.mpf(0)
    N=20000
    for n in range(N+1):
        s0+=n*w-1/(n+alpha)
        s1+=-n*w*psi+mp.log(n+alpha)/(n+alpha)
        w*=(n+a)*(n+c)/((n+b)*(n+1))
        psi+=1/(n+b)
    # Leading analytic tails, used only as numerical acceleration.
    corrected0=s0+(alpha-t)/N
    corrected1=s1+((t-alpha)*(mp.log(N)+1)+alpha-b+mp.mpf(1)/2)/N
    assert abs(corrected0-rhs0)<mp.mpf("1e-7")
    assert abs(corrected1-rhs1)<mp.mpf("1e-6")
    return {"a":textnum(a),"c":textnum(c),"alpha":textnum(alpha),"N":N,
      "q0_value":textnum(rhs0),"q0_first_tail_corrected_residual":textnum(corrected0-rhs0),
      "q1_value":textnum(rhs1),"q1_first_tail_corrected_residual":textnum(corrected1-rhs1),
      "classification":"Finite summation with leading asymptotic tail, not a certified enclosure"}


def uniform_cutoff_checks():
    a,c=mp.mpf(3)/5,mp.mpf(7)/4
    t=a*c+a+c
    cases=[]
    for u in [mp.mpf("0.12"),mp.mpf("-0.12"),mp.mpc("0.06","0.13"),mp.mpf("1e-12")]:
        b=a+c+1+u
        w=mp.gamma(a)*mp.gamma(c)/mp.gamma(b)
        L=mp.gamma(a+1)*mp.gamma(c+1)*mp.gamma(1+u)/(mp.gamma(a+1+u)*mp.gamma(c+1+u))
        A=L/(a*c)
        beta=-t-(a+c+mp.mpf(".5"))*u-u*u/2
        Z=-L*L*(1+u/a)*(1+u/c)/(u*u*(1-u))
        m0=m1=m2=mp.mpf(0)
        rows=[]
        for n in range(5001):
            m0+=w
            m1+=n*w
            m2+=n*n*w
            if n in (1000,5000):
                x=mp.mpf(n+1)
                model=Z+A*x**(1-u)/(1-u)+x**(-u)*(2*L/u**2-A*beta/u-A/2)-x**(-2*u)/(u*u*(1-u*u))
                error=m0*m2-m1*m1-model
                rows.append({"N":n,"residual":textnum(error)})
            w*=(n+a)*(n+c)/((n+b)*(n+1))
        assert abs(error)<mp.mpf(".1")
        cases.append({"u":textnum(u),"rows":rows})
    return {"a":textnum(a),"c":textnum(c),"cases":cases,
            "classification":"Diagnostic convergence of proved uniform expansion, not a certified bound"}


def main():
    result={
      "purpose":"Exact finite checks plus non-certifying high-precision diagnostics",
      "decimal_precision":mp.mp.dps,
      "exact":exact_checks(),
      "cutoff_cases":[cutoff_case(mp.mpf(3)/5,mp.mpf(7)/4),
                      cutoff_case(mp.mpc("0.8","0.2"),mp.mpc("1.1","-0.1"))],
      "polylog_and_endpoints":endpoint_checks(),
      "laurent":laurent_check(mp.mpf(3)/5,mp.mpf(7)/4),
      "generalized_stieltjes_jets":stieltjes_jet_checks(),
      "uniform_cutoff_expansion":uniform_cutoff_checks(),
    }
    OUT.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"status":"pass","output":str(OUT),"exact":result["exact"]},indent=2))


if __name__=="__main__":
    main()
