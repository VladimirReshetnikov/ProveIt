#!/usr/bin/env python3
"""Independent exact recurrence audits and additional numerical examples.
Requires SymPy and mpmath; uses verify.py in the same directory.
High-precision evaluations are tests, not rigorous interval certificates.
"""
from __future__ import annotations
import json
from math import comb
from pathlib import Path
import sympy as s
import mpmath as mp
from verify import involution_coeff, exp_coeff


def multiply(a, b, N):
    return [s.expand(sum(a[j]*b[n-j] for j in range(n+1))) for n in range(N+1)]


def shift(a, k, N):
    return [s.Integer(0)]*k+a[:N+1-k]


def recurrence_residual(coeffs, N=10):
    """Normalize I_n=I_(n-1)+(n-1)I_(n-2) by its positive saddle carrier."""
    terms=[]
    for k in (1,2):
        ds=[]
        for power in range(1,N+1):
            if power%2:
                j=(power+1)//2
                val=s.binomial(s.Rational(1,2),j)*(-k)**j
            else:
                j=power//2
                val=s.Rational(k**(j+1),2*j*(j+1))
            ds.append(val)
        R=[exp_coeff(ds,n) for n in range(N+1)]
        S=[s.Integer(0)]*(N+1)
        for j,aj in enumerate(coeffs):
            for h in range((N-j)//2+1):
                S[j+2*h]+=aj*s.binomial(-s.Rational(j,2),h)*(-k)**h
        product=multiply(R,S,N)
        if k==1:
            terms.append(shift(product,1,N))
        else:
            shifted=shift(product,2,N)
            terms.append([product[n]-shifted[n] for n in range(N+1)])
    full=coeffs+[s.Integer(0)]*(N+1-len(coeffs))
    return [s.factor(full[n]-terms[0][n]-terms[1][n]) for n in range(N+1)]


def zigzag_exact(n):
    vals=[1]
    for j in range(n):
        numerator=sum(comb(j,k)*vals[k]*vals[j-k] for k in range(j+1))+(1 if j==0 else 0)
        assert numerator%2==0
        vals.append(numerator//2)
    return vals[n]


def main():
    out={}
    coeffs=[involution_coeff(j) for j in range(9)]
    residual=recurrence_residual(coeffs)
    assert residual==[0]*11
    out['involution_recurrence_residual_through_t10']=[str(x) for x in residual]
    altered=coeffs.copy(); altered[6]=-s.Rational(562799,47775744)
    bad=recurrence_residual(altered)
    assert bad[:8]==[0]*8
    assert bad[8]==s.Rational(14444755133,114661785600)
    out['displayed_arxiv_v1_coefficient_a6'] = str(altered[6])
    out['replacement_a6_recurrence_residual_t8'] = str(bad[8])
    # Exact check of the quadratic inverse differential formula.
    X,a,q=s.symbols('X a q',positive=True)
    h1=-2/(q-1); h2=q/(q*q-1); gp=1/(2*a*X)
    D=lambda f,n: (s.diff(f,X)-a*n*f)/(2*a*X)
    d1=s.factor(-h1*gp)
    d2=s.factor(-h2*gp+h1*h1*D(gp,2)/2)
    expected=-q/(2*a*(q*q-1)*X)-1/(a*(q-1)**2*X**2)-1/(2*a*a*(q-1)**2*X**3)
    assert s.simplify(d2-expected)==0
    out['q_inverse_d1']=str(d1)
    out['q_inverse_d2']=str(d2)
    mp.mp.dps=90
    aa=mp.pi/2
    for n in range(1,21):
        ss=mp.mpf(n+1)
        factor=(mp.zeta(ss,mp.mpf('.25'))-mp.zeta(ss,mp.mpf('.75')))/mp.power(4,ss) if n%2==0 else (1-mp.power(2,-ss))*mp.zeta(ss)
        got=2*mp.factorial(n)*aa**(-n-1)*factor
        assert abs(got/zigzag_exact(n)-1)<mp.mpf('1e-75')
    out['zigzag_identity_tests']='PASS: parity-resolved formulas at n=1..20'
    rows=[]
    for n in (100,101):
        y=mp.mpf(zigzag_exact(n)); L=mp.log(y/4)
        Z=L/mp.lambertw(L/(mp.e*aa)); lam=mp.log(Z/aa)
        core=Z-mp.mpf('.5')
        c1=1/(24*lam*Z)
        c3=-(14*lam*lam+10*lam+5)/(5760*lam**3*Z**3)
        for name,val in [('core',core),('through Z^-1',core+c1),('through Z^-3',core+c1+c3)]:
            rows.append([n,name,mp.nstr(abs(val-n),10)])
    out['zigzag_inverse_absolute_errors']=rows
    n=30; y=mp.power(2,n)-n-1; aa=mp.log(2); X=mp.log(y)/aa; T=mp.power(2,-X)
    d1=(X+1)/aa
    d2=-(X+1)**2/(2*aa)+(X+1)/aa**2
    out['eulerian_m1_inverse_absolute_errors']=[mp.nstr(abs(X-n),10),mp.nstr(abs(X+d1*T-n),10),mp.nstr(abs(X+d1*T+d2*T*T-n),10)]
    out['numerical_precision_decimal_digits']=mp.mp.dps
    Path(__file__).with_name('audit_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    main()
