#!/usr/bin/env python3
"""Independent floating-point diagnostics, NOT interval certificates.
Run: python code/verify_numeric.py --group core|harmonic|jets|all --dps 50
"""
from __future__ import annotations
import argparse,json,platform,time
from pathlib import Path
import mpmath as mp
import sympy as sp
from continuous_depth import (kernel,kernel_dx,contour_profile,fractional_profile,
 negative_profile,centered_zeta,entire_e,e_jet_at_zero,harmonic_summand)
OUT=Path(__file__).resolve().parents[1]/'data'; OUT.mkdir(exist_ok=True)
p=argparse.ArgumentParser(); p.add_argument('--group',choices=['core','harmonic','jets','all'],default='all'); p.add_argument('--dps',type=int,default=50)
args=p.parse_args()
if args.dps<40: raise ValueError('Use at least 40 working decimal digits')
mp.mp.dps=args.dps; M=mp.mpf; C=mp.mpc; TOL=M('1e-30'); records=[]
def check(name,lhs,rhs,**parameters):
    err=abs(lhs-rhs)/(1+abs(rhs))
    row={'name':name,'parameters':{k:str(v) for k,v in parameters.items()},'lhs':mp.nstr(lhs,args.dps),'rhs':mp.nstr(rhs,args.dps),'scaled_residual':mp.nstr(err,8),'threshold':str(TOL),'pass':bool(err<TOL)}
    records.append(row); print(name,mp.nstr(err,4),row['pass'],flush=True)
    if err>=TOL: raise AssertionError(json.dumps(row,indent=2))
def rq(f): return mp.quad(f,[-mp.inf,-4,0,4,mp.inf])
def ci(r,s,a):
    X=sp.Symbol('X')
    pp=(X*sp.prod(X**2+(2*j*sp.pi)**2 for j in range(1,r//2)) if r%2==0
        else sp.prod(X**2+((2*j-1)*sp.pi)**2 for j in range(1,(r-1)//2+1)))
    terms=[]
    for (power,),coef in sp.Poly(pp,X).terms():
        co=M(str(sp.N(coef,mp.mp.dps)))
        val=(mp.rf(s,power-1)*entire_e(s+power-1,a) if r%2==0
             else mp.rf(s,power)*mp.lerchphi(-1,s+power,a))
        terms.append(co*val/mp.factorial(r-1))
    return mp.fsum(terms)
def core():
    for r in range(1,9):
        x=M('1.1')
        if r%2: val=mp.fprod(x*x+((2*j-1)*mp.pi)**2 for j in range(1,(r-1)//2+1))/(mp.factorial(r-1)*(1+mp.exp(-x)))
        else: val=x*mp.fprod(x*x+(2*j*mp.pi)**2 for j in range(1,r//2))/(mp.factorial(r-1)*(-mp.expm1(-x)))
        check('integer kernel recovery',kernel(r,x),val,rho=r,x=x)
    for r,p in [(M('.7'),C('.4','.2')),(C('1.2','.3'),C('.6','-.3')),(M('2.3'),M('.7'))]:
        check('bilateral Gamma transform',rq(lambda x:mp.exp(-p*x)*kernel(r,x)),mp.exp(r*mp.log(mp.pi/mp.sin(mp.pi*p))),rho=r,p=p)
    for r,s,x in [(M('.4'),M('1.6'),M('.3')),(C('.8','.2'),C('1.3','-.1'),M('-.5')),(M('1.2'),M('2.1'),M(0))]:
        check('ordinary depth convolution',rq(lambda y:kernel(r,y)*kernel(s,x-y)),kernel(r+s,x),rho=r,sigma=s,x=x)
    for r,a,s,x in [(M('.7'),M('1.2'),C('1.3','.2'),M('.2')),(C('1.1','.2'),M('.3'),M('1.2'),M('-.4')),(M('1.4'),M('.5'),M('.6'),M(0))]:
        check('contour versus fractional integral',contour_profile(r,a,s,x),fractional_profile(r,a,s,x),rho=r,a=a,s=s,x=x)
    for r,a in [(M('.6'),M('1.2')),(C('1.4','.2'),M('.3'))]:
        for n in range(3): check('negative spectral resonance',contour_profile(r,a,-n,M('.4')),negative_profile(r,a,n,M('.4')),rho=r,a=a,n=n)
    for r,a,s,x in [(M('.7'),M('.8'),C('1.2','.2'),M('.3')),(C('1.2','.2'),M('.3'),M('-.6'),M('-.4'))]:
        rhs=(x*x+mp.pi**2*r*r)*contour_profile(r,a,s,x)-2*x*s*contour_profile(r,a,s+1,x)+s*(s+1)*contour_profile(r,a,s+2,x)
        check('continuous depth shift',r*(r+1)*contour_profile(r+2,a,s,x),rhs,rho=r,a=a,s=s,x=x)
    for r,a,s in [(2,M('.3'),C('.7','.2')),(3,M('1.2'),M('-.3')),(4,M('.8'),M(0)),(6,M('.5'),M(-2))]:
        check('integer central closure',contour_profile(r,a,s),ci(r,s,a),r=r,a=a,s=s)
    r=M('.6'); sig=2-r; a=M('.8')
    for s,t in [(0,0),(-1,0),(-1,-1)]:
        w=s+t
        for k in range(3):
            lhs=rq(lambda x:x**k*negative_profile(r,a,-s,x)*negative_profile(sig,a,-t,-x))
            if k==0: rhs=entire_e(w,a)
            elif k==1: rhs=(sig*s-r*t)*entire_e(w+1,a)/2
            else:
                q=(sig*(sig+1)*s*(s+1)+r*(r+1)*t*(t+1)-2*r*sig*s*t)/6
                rhs=mp.pi**2*r*sig*entire_e(w,a)/3+q*entire_e(w+2,a)
            check('direct weighted Gamma convolution',lhs,rhs,s=s,t=t,k=k,rho=r,a=a)
def harmonic():
    for r in [M('.7'),C('1.4','.2'),M('2.2')]:
        h=r/2
        for m in range(3):
            coeff=[1,mp.zeta(2,h),(mp.zeta(2,h)**2+mp.zeta(4,h))/2][m]
            check('centered odd Gamma identity',centered_zeta(r,2*m+1),mp.gamma(h)**2*coeff/(2*mp.gamma(r)),rho=r,m=m)
    for r,w in [(M('.7'),M('.4')),(C('1.2','.2'),C('.6','.15'))]:
        val=2*(2*mp.pi)**(r+w-2)*mp.gamma(1-w)*mp.cos(mp.pi*w/2)*centered_zeta(r,1-w)
        check('Fourier-Mellin reflection',fractional_profile(r,M('.5'),w),val,rho=r,w=w)
    for r in [M('.7'),C('1.3','.2')]:
        for m in range(3):
            val=mp.pi**(r+2*m)*[1,r/2,r*(3*r+2)/24][m]/2
            check('odd spectral polynomial value',fractional_profile(r,M('.5'),2*m+1),val,rho=r,m=m)
    rows=json.loads((OUT/'harmonic_coefficients.json').read_text())
    for m,q in [(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,2)]:
        row=next(x for x in rows if (x['m'],x['q'])==(m,q))
        val=M(str(sp.N(sp.sympify(row['simplified_exact_value']),mp.mp.dps)))
        check('alternating harmonic jet',mp.nsum(lambda k:harmonic_summand(k,m,q),[1,mp.inf],method='alternating'),val,m=m,q=q)
    for eps in [M('.2'),C('-.15','.1')]:
        lhs=mp.nsum(lambda k:(-1)**(k-1)*mp.rf(1+eps,k)/mp.gamma(k+1)/k**2*(1+eps/(2*k))**(-3),[1,mp.inf],method='alternating')
        h=1+eps/2
        check('full harmonic generating identity',lhs,mp.gamma(h)**2*mp.zeta(2,h)/(2*mp.gamma(1+eps)),epsilon=eps)
    r=M('.7'); m=1
    def pg(x):
        g=kernel(r,x)*mp.exp(-x/2)*mp.gamma(r)/(2*mp.pi)**(r-2)
        z=1j*mp.exp(-x/2)
        return g*(mp.polylog(3,z)-mp.polylog(3,-z))/1j
    check('odd polylogarithm Gamma integral',rq(pg),mp.gamma(r)*mp.pi**5/2**(r+1)*(r+1)/2,rho=r,m=m)
def jets():
    for a in [M('.3'),M('1.2')]:
        for m in range(1,5): check('central Stieltjes jet',contour_profile(2,a,0,order_jet=m),e_jet_at_zero(m,a),a=a,m=m)
    for r in [M('.5'),M('1.3')]:
        a=M('.8'); sig=2-r; c=M('.6')
        def itg(t):
            pp=c+1j*t; g=mp.pi/mp.sin(mp.pi*pp); v=mp.pi*mp.cot(mp.pi*pp); A=pp+a-1; L=mp.log(A)
            return g*g*((r*(r+1)*g*g-r*r*mp.pi**2)*L*L-(2*r*v/A+1/A**2)*L)
        lhs=mp.quad(itg,[-mp.inf,-2,0,2,mp.inf])/(2*mp.pi)
        val=-2*mp.pi**2*r*sig*mp.stieltjes(1,a)/3+(1-r*sig)*mp.zeta(3,a)+(2-2*r*sig/3)*mp.diff(lambda z:mp.zeta(z,a),3)
        check('mixed Stieltjes second moment',lhs,val,rho=r,a=a)
    for r,a,x in [(M('.7'),M('1.1'),M('.3')),(M(2),M('.8'),M(0))]:
        q0=kernel(r,x)
        def sub(u,j):
            if u==0: return mp.mpf(0)
            return (mp.exp(-(a-1)*u)*kernel(r,x-u)-q0*mp.exp(-u))*mp.log(u)**j/u
        j1=mp.quad(lambda u:sub(u,0),[0,1,4,mp.inf])
        j2=2*mp.quad(lambda u:sub(u,1),[0,1,4,mp.inf])+2*mp.euler*j1
        for order,val in [(1,j1),(2,j2)]: check('subtracted Mellin jet',val,contour_profile(r,a,0,x,order_jet=order),rho=r,a=a,x=x,order=order)
    for r,x in [(M(1),M(0)),(M(2),M('.7'))]:
        z1=r/2+1j*x/(2*mp.pi); z2=r/2-1j*x/(2*mp.pi)
        A1=mp.log(2*mp.pi)-mp.digamma(r)+(mp.digamma(z1)+mp.digamma(z2))/2
        A2=-mp.polygamma(1,r)+(mp.polygamma(1,z1)+mp.polygamma(1,z2))/4
        for order,val in [(1,A1),(2,A1*A1+A2)]: check('polygamma depth jet',mp.diff(lambda z:kernel(z,x),r,order),kernel(r,x)*val,rho=r,x=x,order=order)
    a=M('1.3'); b=M('.7')
    for s in [M('.4'),M(1),C('1.2','.2')]:
        val=mp.digamma(a)-mp.digamma(b) if s==1 else mp.zeta(s,b)-mp.zeta(s,a)
        check('anchored central primitive',mp.quad(lambda z:entire_e(s,z),[b,a]),val,s=s,a=a,b=b)
    check('Stieltjes Gamma primitive',mp.quad(lambda z:-mp.digamma(z),[b,a]),mp.loggamma(b)-mp.loggamma(a),a=a,b=b)
for group in (['core','harmonic','jets'] if args.group=='all' else [args.group]):
    records=[]; start=time.monotonic(); globals()[group]()
    result={'status':'PASS','group':group,'working_decimal_digits':args.dps,'mpmath_version':mp.__version__,'python_version':platform.python_version(),'diagnostic_count':len(records),'threshold':str(TOL),'results':records,'elapsed_seconds':round(time.monotonic()-start,2),'evidentiary_limit':'Floating-point diagnostics, not rigorous enclosures or proofs.'}
    (OUT/f'numeric_{group}.json').write_text(json.dumps(result,indent=2)+'\n'); print('GROUP',group,len(records),'PASS',flush=True)
