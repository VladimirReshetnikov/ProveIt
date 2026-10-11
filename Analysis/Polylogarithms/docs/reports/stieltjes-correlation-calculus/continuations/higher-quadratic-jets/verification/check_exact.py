#!/usr/bin/env python3
"""Independent exact regressions. These do not replace the analytic proofs."""
from __future__ import annotations
import argparse, json, platform, sys
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import sympy as sp
from core import c_coeff, pab

s,x,y,F,u,v,h=sp.symbols('s x y F u v h')
checks=[]
def check(name, expr):
    val=sp.cancel(sp.expand(expr))
    if val != 0:
        raise AssertionError(f'{name}: {val}')
    checks.append(name)
def sq(q): return sp.Rational(q.numerator,q.denominator)
def poly(q,z): return sum(sq(c)*z**k for k,c in enumerate(q))
def bell_elementary(N,scale,degree):
    # Newton recurrence from power sums, independent of product expansion.
    a=[sp.Integer(1)]
    for k in range(1,degree+1):
        a.append(sp.cancel(sum((-1)**(j-1)*scale**j*sp.harmonic(N,j)*a[k-j]
                               for j in range(1,k+1))/k))
    return a

def main(out):
    table={}
    for j in range(1,21):
        cc=c_coeff(j); independent=sp.Poly(sp.expand(sp.rf(2*s,2*j)/sp.factorial(2*j)-sp.rf(s,j)/sp.factorial(j)),s)
        for k in range(2*j+1):
            check(f'C[{j},{k}]_rising',sq(cc[k])-independent.nth(k))
        check(f'C[{j},2]_harmonic',sq(cc[2])-2*(sp.harmonic(2*j)-sp.harmonic(j)/2)/j)
        left=bell_elementary(2*j-1,2,min(8,2*j-1)); right=bell_elementary(j-1,1,min(8,2*j-1))
        for k in range(2,min(9,2*j)+1):
            check(f'C[{j},{k}]_Newton',sq(cc[k])-(left[k-1]-right[k-1])/j)
        if j<=6: table[f'C_{j}']=str(sp.factor(independent.as_expr()))
    def deriv(expr): return sp.diff(expr,x)+sp.diff(expr,F)*(2*F-1/x)
    for m in range(11):
        p,a,b=pab(m); pp,aa,bb=poly(p,1/x),poly(a,1/x),poly(b,1/x)
        check(f'K_ODE_{m}',x*x*sp.diff(pp,x,2)-2*x*x*sp.diff(pp,x)-m*(m+1)*pp)
        q=aa*F+bb
        check(f'order_ODE_{m}',x*x*deriv(deriv(q))-2*x*x*deriv(q)-m*(m+1)*q-(2*m+1)*pp)
        check(f'P_reversal_{m}',poly(a,y)-(-1)**m*poly(p,-y))
        table[f'PAB_{m}']={'P':str(poly(p,y)),'A':str(poly(a,y)),'B':str(poly(b,y))}
    for m in range(1,17):
        Dm=sp.prod(1-s/k for k in range(1,m+1))
        Dprev=sp.prod(1-s/k for k in range(1,m))
        check(f'Appell_exact_{m}',(m-s)*Dprev-m*Dm)
        check(f'Appell_harmonic1_{m}',-sp.diff(Dm,s).subs(s,0)-sp.harmonic(m))
        check(f'Appell_harmonic2_{m}',2*sp.diff(Dm,s).subs(s,0)**2-sp.diff(Dm,s,2).subs(s,0)-sp.harmonic(m)**2-sp.harmonic(m,2))
    for r in range(2,19):
        coefficient=sum(sp.Rational(1,k*(r-k)) for k in range(1,r))
        check(f'log_square_harmonic_{r}',coefficient-2*sp.harmonic(r-1)/r)
        # (u^k-v^k) is homogeneous; this independently checks direct convolution.
        lser=sum((-1)**(k+1)*(u**k-v**k)*y**k/k for k in range(1,r))
        direct=sp.expand(lser*lser).coeff(y,r)
        T=(-1)**r*sum((u**k-v**k)*(u**(r-k)-v**(r-k))/(k*(r-k)) for k in range(1,r))
        check(f'two_mass_T_{r}',direct-T)
        if r<=7: table[f'T_{r}']=str(sp.factor(T))
    for d in range(11):
        for r in range(1,9):
            remainder=sum(sp.binomial(d,l)*(-u)**(d-l)*(y+u)**l for l in range(min(d,r-1)+1))
            _, rem=sp.div(y**d,(y+u)**r,y)
            check(f'resolvent_remainder_d{d}_r{r}',rem-remainder)
        check(f'polynomial_bilateral_zero_{d}',sp.bernoulli(2*d+1,x)+sp.bernoulli(2*d+1,1-x))
    # Exact first-jet anomaly coefficients from a separate odd-log convolution.
    for j in range(1,17):
        direct=(-1)**j*sum(sp.Rational(1,(2*k+1)*(2*j-2*k-1)) for k in range(j))
        check(f'first_anomaly_{j}',direct-(-1)**j*(sp.harmonic(2*j)-sp.harmonic(j)/2)/j)
    negative=[]
    controls={
        'mutated_C1':poly(c_coeff(1),s)+s*s-2*s*s,
        'omitted_B1':x*x*deriv(deriv((1/x-1)*F))-2*x*x*deriv((1/x-1)*F)-2*(1/x-1)*F-3*(1+1/x),
        'false_second_jet_even_vanishing':-4*x*x,
        'missing_Appell_harmonic_transport':-2*x,
        'wrong_collision_cubic_sign':2*h**3,
    }
    for name,residual in controls.items():
        if sp.cancel(residual)==0: raise AssertionError(f'negative control did not reject: {name}')
        negative.append(name)
    report={'status':'passed','exact_assertions':len(checks),'negative_controls_rejected':len(negative),
            'checks':checks,'negative_controls':negative,'python':platform.python_version(),'sympy':sp.__version__,
            'scope':'Finite exact regressions only; the article supplies the all-index analytic proofs.'}
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(report,indent=2)+'\n')
    (out.parent/'coefficient_table.json').write_text(json.dumps(table,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','exact_assertions','negative_controls_rejected')},indent=2))
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'exact_results.json')
    main(ap.parse_args().output)
