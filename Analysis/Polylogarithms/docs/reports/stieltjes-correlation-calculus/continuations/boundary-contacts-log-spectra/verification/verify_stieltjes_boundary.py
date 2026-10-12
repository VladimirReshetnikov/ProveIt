#!/usr/bin/env python3
"""Independent checks of the p=1,q=-1 Stieltjes boundary-derivative identity.

Requires SymPy and mpmath plus the companion verify_contacts.py coefficient
module. Numerical evidence includes an independent Laplace integral for the
alternating-Hurwitz order derivative and direct finite summation.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import platform
import time
import sympy as sp
import mpmath as mp
from verify_contacts import bk, p, q, s, mprat


def coefficients(K):
    # q is fixed at -1; p remains AMBIENT and independent until differentiating.
    cs, es = [], []
    for k in range(K+1):
        poly = sp.expand(sum(
            bk(j,p,-sp.Rational(1,2))*bk(k-j,-sp.Integer(1),sp.Rational(1,2))+
            bk(j,p,sp.Rational(1,2))*bk(k-j,-sp.Integer(1),-sp.Rational(1,2))
            for j in range(k+1))/4)
        cs.append(sp.factor(poly.subs(p,1)))
        es.append(sp.factor(sp.diff(poly,p).subs(p,1)))
    return cs,es


def exact():
    L,g,u,e,z=sp.symbols('L g u e z',positive=True)
    assertions=[]
    def chk(name,expr):
        assert sp.simplify(expr)==0,(name,expr)
        assertions.append(name)
    eta=sp.series((1-sp.exp(-L*u))*(1/u+g),u,0,2).removeO()
    chk('eta value at one',eta.coeff(u,0)-L)
    chk('eta first derivative at one',eta.coeff(u,1)-(g*L-L**2/2))
    raw=(z**p-(z-1)**p)*sp.exp(-2*p*e)
    W=sp.exp(-2*e)*(z*sp.log(z)-(z-1)*sp.log(z-1)-2*e)
    chk('W is independent spectral derivative',sp.diff(raw,p).subs(p,1)-W)
    lam=(p+q)/2
    counter=sp.diff(-sp.Rational(1,2)*(z-1)**(-lam)+
                    sp.Rational(1,2)*z**(-lam),p).subs({p:1,q:-1})
    chk('logarithmic subtraction sign',counter+
        (sp.log(z)-sp.log(z-1))/4)
    r=sp.sqrt(2/sp.pi)
    T1=r*(e*L+g*L-L**2/2)
    T2=(-e*(1-L)-g*L+L**2/2)/r
    endpoint=T1*3*r/4+T2/(4*r)
    proposed=3/(2*sp.pi)*(L*(g+e)-L**2/2)+sp.pi/8*(-e*(1-L)-g*L+L**2/2)
    chk('explicit endpoint evaluation',endpoint-proposed)
    cs,es=coefficients(10)
    chk('leading endpoint coefficient c2',cs[2]+sp.Rational(1,16))
    chk('leading independent derivative c2p',es[2]+sp.Rational(1,16))
    for k in [1,3,5,7,9]:
        chk(f'odd endpoint coefficient k={k}',cs[k])
        chk(f'odd endpoint derivative k={k}',es[k])
    return {'kind':'exact symbolic verification','status':'passed',
            'assertion_count':len(assertions),'assertions':assertions,
            'endpoint_coefficients':[str(x) for x in cs],
            'endpoint_p_derivatives':[str(x) for x in es],
            'versions':{'python':platform.python_version(),'sympy':sp.__version__}}


def numeric():
    start=time.time();mp.mp.dps=80
    records=[]
    def check(name,left,right,tol):
        err=abs(left-right)
        assert err<mp.mpf(tol),(name,mp.nstr(err,15))
        records.append({'name':name,'absolute_error':mp.nstr(err,12),
                        'tolerance':str(tol),'status':'passed'})
    gamma=mp.euler;L=mp.log(2)
    def hh(z): return mp.sqrt(2)*mp.gamma((z+1)/2)/mp.gamma(z/2)
    def b1(z): return (mp.digamma((z+1)/2)-mp.digamma(z/2))/2
    def t_stieltjes(z):
        hz=hh(z);ell=mp.log(hz)
        d0=-mp.digamma(z/2)+mp.digamma((z+1)/2)
        d1=mp.stieltjes(1,z/2)-mp.stieltjes(1,(z+1)/2)
        return hz/2*((ell-L)*d0-d1)
    def t_laplace(z):
        bp=mp.quad(lambda y:mp.exp(-y)/(1+mp.exp(-y/z))*
                   (mp.log(y)-mp.log(z)+gamma),[0,1,mp.inf])/z
        return hh(z)*(mp.log(hh(z))*b1(z)+bp)
    for z in [mp.mpf(1),mp.mpf(2),mp.mpf('3.5'),mp.mpf(9)]:
        check(f'generalized-Stieltjes T versus independent Laplace integral, z={z}',
              t_stieltjes(z),t_laplace(z),'1e-65')

    ell1=mp.log(mp.sqrt(2/mp.pi))
    rhs=3/(2*mp.pi)*(L*(gamma+ell1)-L**2/2)+\
        mp.pi/8*(-ell1*(1-L)-gamma*L+L**2/2)
    check('closed endpoint constant versus direct generalized Stieltjes values',
          t_stieltjes(mp.mpf(1))*3*mp.sqrt(2/mp.pi)/4+
          t_stieltjes(mp.mpf(2))/(4*mp.sqrt(2/mp.pi)),rhs,'1e-65')

    # Generate only integer h,B1,B1-order-derivative values by their exact
    # recurrences, initialized with eta(1),eta'(1). This summation route is
    # independent of evaluating generalized Stieltjes constants at each term.
    N=256;H={1:mp.sqrt(2/mp.pi)};B={1:L};Q={1:gamma*L-L**2/2}
    for j in range(1,N+4):
        H[j+1]=mp.mpf(j)/H[j]
        B[j+1]=mp.mpf(1)/j-B[j]
        Q[j+1]=-mp.log(j)/j-Q[j]
    T={j:H[j]*(mp.log(H[j])*B[j]+Q[j]) for j in H}
    R={j:(mp.mpf(j)-mp.mpf('.5'))/(2*H[j]) for j in H}
    terms=[]
    for j in range(2,N+3):
        z=mp.mpf(j);hz=H[j];ell=mp.log(hz)
        A=1/hz**2-hz**2/(z*(z-1))
        W=(z*mp.log(z)-(z-1)*mp.log(z-1)-2*ell)/hz**2
        terms.append(R[j]*(W*hz*B[j]+A*T[j])-mp.log(z/(z-1))/4)
    partial=mp.fsum(terms);X=mp.mpf(N+2)
    exact_tail=T[N+2]*R[N+3]+T[N+3]*R[N+2]+mp.log(X)/4
    check('257-term direct ordinary sum plus exact endpoint remainder',
          partial+exact_tail,rhs,'1e-65')
    cs,es=coefficients(10)
    tail=mp.fsum((mprat(es[k])-mprat(cs[k])*mp.log(X)/2)*X**(-k)
                for k in range(1,11))
    check('257-term direct ordinary sum plus degree-10 asymptotic remainder',
          partial+tail,rhs,'1e-23')
    leading=(mp.log(X)-2)/(32*X**2)
    records.append({'name':'leading tail diagnostic (log X - 2)/(32 X^2)',
                    'remainder_after_leading_term':mp.nstr(exact_tail-leading,14),
                    'ordinary_partial_sum':mp.nstr(partial,45),
                    'closed_value':mp.nstr(rhs,45),'status':'recorded'})
    return {'kind':'independent numerical diagnostics','status':'passed',
            'precision_decimal_digits':mp.mp.dps,'diagnostic_count':len(records),
            'diagnostics':records,
            'evidence_boundary':'Decimal diagnostics; no interval certificate.',
            'versions':{'python':platform.python_version(),'mpmath':mp.__version__},
            'seconds':round(time.time()-start,4)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent/'results')
    parser.add_argument('--exact-only',action='store_true')
    parser.add_argument('--numeric-only',action='store_true')
    args=parser.parse_args();args.output_dir.mkdir(parents=True,exist_ok=True)
    if args.exact_only and args.numeric_only:
        parser.error('Choose at most one mode selector.')
    if not args.numeric_only:
        e=exact();(args.output_dir/'stieltjes_boundary_exact.json').write_text(json.dumps(e,indent=2)+'\n')
        print(f"Stieltjes exact: {e['assertion_count']} assertions passed.",flush=True)
    if not args.exact_only:
        n=numeric();(args.output_dir/'stieltjes_boundary_numeric.json').write_text(json.dumps(n,indent=2)+'\n')
        print(f"Stieltjes numerical: {n['diagnostic_count']} diagnostics passed.",flush=True)
if __name__=='__main__':main()
