#!/usr/bin/env python3
"""Exact symbolic audits of the local and inverse coefficients.
Writes a JSON log to --output; never accesses the network.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
import sympy as s

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data')
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    u,x,a,eps=s.symbols('u x a eps',positive=True)
    m,k,b,k1,h2=s.symbols('m k b k1 h2',nonzero=True)
    # Put t=u^2 so all computations are ordinary power-series calculations.
    w=s.series(1-s.exp(-u*u),u,0,7).removeO()
    Q=1-m*w+k*u**3*(w/u**2)**s.Rational(3,2)+b*w*w+k1*u**5*(w/u**2)**s.Rational(5,2)
    hs=s.series(-s.log(Q),u,0,6).removeO().expand()
    assert s.simplify(hs.coeff(u,2)-m)==0
    assert s.simplify(hs.coeff(u,3)+k)==0
    assert s.simplify(hs.coeff(u,4)-((m*m-m)/2-b))==0
    # Inversion in v=h/m, with v=u^2.
    t=u*u+k/m*u**3+(s.Rational(3,2)*k*k/m**2-h2/m)*u**4
    residual=s.series(m*t-k*u**3*(t/u**2)**s.Rational(3,2)+h2*t*t-m*u*u,u,0,5).removeO()
    assert s.simplify(residual)==0
    # First cut-integral correction.
    E=1+eps*(x*x/2-x)
    H=m+b*eps*x
    B=k-k1*eps*x
    den=(a+x*H/m)**2+eps*x**3*B**2/m**2
    actual=s.diff((B/k)*E/den,eps).subs(eps,0)
    expected=(x*x/2-x-k1*x/k-2*b*x*x/(m*(a+x))-k*k*x**3/(m*m*(a+x)**2))/(a+x)**2
    assert s.factor(actual-expected)==0
    # F'(w) coefficient check with w=u^2.
    dF=s.series(s.log((1+u)/2)/(1-u*u),u,0,5).removeO()
    assert dF.coeff(u,1)==1 and dF.coeff(u,3)==s.Rational(4,3)
    # Density response: Delta=3 k/(2m) sqrt(t)+O(t).
    A=3*k/(2*m)
    assert s.simplify(m/A**2-4*m**3/(9*k*k))==0
    # Incomplete-gamma tail center about the exact Lambert core w0=1/u.
    power=s.Rational(5,2)
    delta=-power*u+(s.Rational(3,2)*power**2+power)*u*u
    inv_w=u/(1+u*delta)
    tail=1-power*inv_w+power*(power+1)*inv_w**2
    center_residual=s.series(delta+power*s.log(1+u*delta)-s.log(tail),u,0,3).removeO()
    assert s.simplify(center_residual)==0
    log={'sympy':s.__version__,'checks':{
        'h(t)_through_t_squared':'PASS','inverse_through_v_squared':'PASS',
        'first_cut_kernel':'PASS','odd_F_coefficients':'PASS','density_response':'PASS','incomplete_gamma_center':'PASS'},
        'h_t_five_halves':str(s.factor(hs.coeff(u,5))),
        'scope':'Exact symbolic identities only; not a proof of contour or probabilistic limits.'}
    (args.output/'symbolic_audit.json').write_text(json.dumps(log,indent=2),encoding='utf-8')
    print(json.dumps(log,indent=2))
if __name__=='__main__':main()
