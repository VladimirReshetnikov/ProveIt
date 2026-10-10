#!/usr/bin/env python3
"""Exact coefficient checks and optional reflected-moment diagnostics.

Default: exact symbolic identities. --diagnostics: high precision improper
quadrature in t and independent quadrature in x on six selected cases.
Floating point results are diagnostics, not interval certificates.
"""
import argparse
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]


def exact_checks():
    L,q,g,A,B = s.symbols("L q gamma A B", nonzero=True)
    C=A-g
    h1=q*(-C+g/L)
    h2=q*(C-2*g/L-2*g/L**2)
    local=-g*q+q*q*(B+g*A-g*g/(2*L))+h1+L*(h2+h1*h1)/2
    P1=L*(C*q+C*C*q*q)/2-(A+g)*q+(B+g*g)*q*q
    assert s.expand(local-P1)==0
    e=s.exp(C*q)
    D=lambda v:q*s.diff(v,q)
    op=(g*A+B)*q*q*e-g*q*(D(e)+2*e)+L*D(D(e))/2-D(e)
    assert s.simplify(op/e-P1)==0
    k=s.symbols("k",positive=True)
    moments={}
    for j in range(1,5):
        mom=s.expand(sum(s.binomial(j,h)*(-L)**(j-h)*s.rf(k*L+1,h)/k**h for h in range(j+1)))
        moments[str(j)]=str(mom)
    expected=[1/k,L/k+2/k**2,5*L/k**2+6/k**3,3*L**2/k**2+26*L/k**3+24/k**4]
    assert all(s.expand(s.sympify(moments[str(j)],locals={"k":k,"L":L})-expected[j-1])==0 for j in range(1,5))
    result={"status":"PASS","arithmetic":"exact symbolic rational algebra", "sympy_version":s.__version__,"checks":6,"coefficient":str(s.expand(P1)),"shifted_gamma_raw_moments":moments}
    (ROOT/"data"/"gamma_exact.json").write_text(json.dumps(result,indent=2)+"\n")
    print("PASS: 6 exact gamma-transition coefficient and moment checks",flush=True)


def diagnostics():
    import mpmath as mp
    mp.mp.dps=65
    g=mp.euler;A=mp.zeta(2)/(2*g);B=mp.zeta(3)/(3*g)-A*A/2;C=A-g
    cutoff=mp.mpf("1e-12")

    def loggamma_unit(x):
        y=1-x
        if y<cutoff:
            return g*y+sum(mp.zeta(j)*y**j/j for j in range(2,8))
        return mp.loggamma(x)

    rows=[]
    for c_int in [0,1,-1]:
        for m_int in [20,100,500,2000]:
            m=mp.mpf(m_int);c=mp.mpf(c_int);L=mp.log(m)+c;q=mp.exp(-c);k=m+1;n=k*L
            logbase=m*mp.log(g)+mp.loggamma(n+1)-(n+1)*mp.log(k)

            def scaled_x(x):
                if x<=0 or x>=1:return mp.mpf(0)
                f=loggamma_unit(x);h=loggamma_unit(1-x)
                if f<=0 or h<=0:return mp.mpf(0)
                return mp.exp(n*mp.log(f)+m*mp.log(h)-logbase)

            def scaled_t(t):
                if t<=0 or t==mp.inf:return mp.mpf(0)
                x=mp.exp(-t)
                return scaled_x(x)*x

            sd=mp.sqrt(L/k)
            finite=sorted(set(v for v in [L/2,L-8*sd,L-2*sd,L,L+2*sd,L+8*sd,2*L,max(4*L,mp.mpf(20))] if v>0))
            ratio=mp.quad(scaled_t,[mp.mpf(0)]+finite+[mp.inf])
            limit=mp.exp(C*q)
            P1=L*(C*q+C*C*q*q)/2-(A+g)*q+(B+g*g)*q*q
            row={"m":m_int,"c":c_int,"n":mp.nstr(n,45),"L":mp.nstr(L,45),"ratio_t":mp.nstr(ratio,45),"limit":mp.nstr(limit,45),"first_correction":mp.nstr(limit*(1+P1/m),45),"scaled_relative_error":mp.nstr((ratio/limit-1-P1/m)*m*m/(L*L),30)}
            if m_int in [20,100]:
                xbreaks=sorted(set([mp.mpf(0),mp.mpf(1)]+[mp.exp(-v) for v in finite]))
                ratio_x=mp.quad(scaled_x,xbreaks)
                discrepancy=abs(ratio-ratio_x)/abs(ratio)
                assert discrepancy<mp.mpf("1e-35"), (m_int,c_int,discrepancy)
                row.update({"ratio_x":mp.nstr(ratio_x,45),"relative_coordinate_discrepancy":mp.nstr(discrepancy,12)})
            rows.append(row)
            print(f"diagnostic m={m_int}, c={c_int}: ratio={mp.nstr(ratio,18)}",flush=True)
    result={"status":"PASS numerical diagnostics", "precision_decimal_digits":mp.mp.dps,"mpmath_version":mp.__version__,"interpretation":"Uncertified floating point improper quadrature; six cases checked in two coordinate systems. Analytic asymptotic bounds come from the article.","C":mp.nstr(C,45),"rows":rows}
    (ROOT/"data"/"gamma_diagnostics.json").write_text(json.dumps(result,indent=2)+"\n")


if __name__=="__main__":
    parser=argparse.ArgumentParser();parser.add_argument("--diagnostics",action="store_true");args=parser.parse_args()
    exact_checks()
    if args.diagnostics:diagnostics()
