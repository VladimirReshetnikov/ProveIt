#!/usr/bin/env python3
"""Exact algebra certificates and independent numerical diagnostics.

Run from any directory: python verification/verify.py [--exact-only|--numeric-only]
Exact checks prove finite polynomial identities only. Floating-point checks are
not interval certificates and do not substitute for the article's analytic proofs.
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
import platform
from typing import Any
import mpmath as mp
import sympy as sp
from sympy.functions.combinatorial.numbers import stirling

OUT = Path(__file__).resolve().parent

def exact_suite() -> dict[str, Any]:
    X, t, x = sp.symbols('X t x')
    zs = {j: sp.Symbol(f'z{j}') for j in range(2, 13)}
    # Exponential coefficients by the logarithmic-derivative recurrence.
    def exp_coeff(logc: dict[int, sp.Expr], N: int) -> list[sp.Expr]:
        c = [sp.S.One]
        for n in range(1, N+1):
            c.append(sp.expand(sum(j*logc.get(j,0)*c[n-j] for j in range(1,n+1))/n))
        return c
    N=10
    logs={1:X, **{j:(-1)**j*zs[j]/j for j in range(2,N+1)}}
    c=exp_coeff(logs,N)
    P=[sp.expand(sp.factorial(n)*c[n+1]) for n in range(N)]
    # Independent complete Bell-polynomial recurrence.
    bs={j:sp.factorial(j)*logs[j] for j in range(1,N+1)}
    bells=[sp.S.One]
    assertions=[]
    def check(name: str, value: sp.Expr) -> None:
        if sp.expand(value)!=0:
            raise AssertionError(f'{name}: {sp.expand(value)}')
        assertions.append(name)
    for n in range(1,N+1):
        bells.append(sp.expand(sum(sp.binomial(n-1,j-1)*bs[j]*bells[n-j] for j in range(1,n+1))))
        check(f'Bell_vs_exponential_degree_{n}', bells[n]-sp.factorial(n)*c[n])
    # Independent bivariate Gamma quotient, computed as A(u)A(v)/A(u+v).
    lg={j:(-1)**j*zs[j]/j for j in range(2,N+1)}
    A=exp_coeff(lg,N); C=exp_coeff({j:-v for j,v in lg.items()},N)
    B={}
    for i in range(6):
        for j in range(6):
            if i+j<=N:
                B[i,j]=sp.expand(sum(A[i-p]*A[j-q]*C[p+q]*sp.binomial(p+q,p)
                    for p in range(i+1) for q in range(j+1)))
    def b(i:int,j:int)->sp.Expr:
        return B.get((i,j),sp.S.Zero) if i>=0 and j>=0 else sp.S.Zero
    catalog=[]
    for n in range(5):
        for m in range(5):
            coefficients={}
            rhs=b(n+1,m+1)
            constant=sp.expand(sp.factorial(n)*sp.factorial(m)*rhs)
            for k in range(n+m+2):
                ck=sp.expand(sp.factorial(n)*sp.factorial(m)/sp.factorial(k)*sum(
                    sp.binomial(k+1,r)*b(n+1-r,m-k+r) for r in range(k+2)))
                if ck:
                    coefficients[str(k)]=str(ck)
                    rhs += ck*P[k]/(sp.factorial(n)*sp.factorial(m))
            rhs=sp.expand(rhs*sp.factorial(n)*sp.factorial(m))
            check(f'product_G{n}_G{m}',P[n]*P[m]-rhs)
            top=sp.Rational(n+m+2,(n+1)*(m+1))
            check(f'top_coefficient_G{n}_G{m}',sp.sympify(coefficients[str(n+m+1)])-top)
            catalog.append({'left':[n,m],'I':str(constant),'G':coefficients})
    # Printed low-index laws; fourth uses the exact even-zeta relation z2^2=5*z4/2.
    z2,z3,z4=zs[2],zs[3],zs[4]
    check('printed_G0_G0',P[0]**2-(2*P[1]-z2))
    check('printed_G0_G1',P[0]*P[1]-(sp.Rational(3,2)*P[2]-z2*P[0]+z3))
    check('printed_G0_G2',P[0]*P[2]-(sp.Rational(4,3)*P[3]-2*z2*P[1]+2*z3*P[0]-2*z4))
    fourth=sp.expand(P[1]**2-(P[3]-2*z2*P[1]+2*z3*P[0]-z4/4))
    check('printed_G1_G1_even_zeta_relation',fourth.subs(z4,sp.Rational(2,5)*z2**2))
    # Elementary-symmetric coefficients vs unsigned Stirling numbers.
    es={}
    for k in range(1,13):
        polynomial=sp.Poly(sp.prod(1+t/sp.Integer(j) for j in range(1,k+1)),t)
        es[k]=[polynomial.nth(j) for j in range(k+1)]
        for j in range(k+1):
            check(f'elementary_Stirling_k{k}_j{j}',es[k][j]-stirling(k+1,j+1,kind=1)/sp.factorial(k))
    # Direct differentiation of the singular part independently checks the signs.
    for k in range(1,7):
        for n in range(7):
            rhs=(-1)**k*sp.factorial(k)*sp.factorial(n)/x**(k+1)*sum(
                (-1)**i*es[k][i]*sp.log(x)**(n-i)/sp.factorial(n-i)
                for i in range(min(k,n)+1))
            check(f'singular_parameter_derivative_k{k}_n{n}',sp.diff(sp.log(x)**n/x,x,k)-rhs)
    # Log-Gamma convolution powers: squarefree differentiation vs one-variable Bell form.
    y=sp.symbols('EulerGamma')
    gamma_powers=[]
    for d in range(2,8):
        H=sp.harmonic(d-1)
        logden={1:H-y, **{j:sp.harmonic(d-1,j)/j-zs[j]/j for j in range(2,d+1)}}
        den=exp_coeff(logden,d)
        final=exp_coeff({1:H, **{j:sp.harmonic(d-1,j)/j-zs[j]/j for j in range(2,d+1)}},d)
        co=[]
        for j in range(d+1):
            # Choose which derivatives hit numerator Gamma factors; remaining hit zeta/denominator.
            raw=sum(sp.binomial(d,a)*y**a*sp.factorial(d-a)*den[d-a-j]/sp.factorial(j)
                    for a in range(d-j+1))/sp.factorial(d-1)
            target=sp.factorial(d)*final[d-j]/sp.factorial(j)/sp.factorial(d-1)
            check(f'gamma_power_d{d}_jet{j}',raw-target)
            co.append(str(sp.expand(target)))
        gamma_powers.append({'d':d,'jet_coefficients':co})
    document={'convention':'zj denotes zeta(j); I is delta_0-1; products are circle convolutions',
        'stieltjes_products':catalog,'gamma_convolution_powers':gamma_powers}
    (OUT/'identity_catalog.json').write_text(json.dumps(document,indent=2)+'\n')
    return {'status':'passed','assertion_count':len(assertions),'assertions':assertions,
            'scope':'finite exact polynomial identities, not formalized analytic theorems'}


def numeric_suite(dps:int=45) -> dict[str,Any]:
    if dps<35: raise ValueError('At least 35 decimal digits are required for this diagnostic suite.')
    mp.mp.dps=dps
    results=[]
    def check(name:str,a:Any,b:Any)->None:
        err=abs(a-b); scaled=err/(1+abs(b))
        if not mp.isfinite(scaled) or scaled>mp.mpf('1e-28'):
            raise AssertionError(f'{name}: scaled residual {scaled}')
        results.append({'name':name,'lhs':mp.nstr(a,32),'rhs':mp.nstr(b,32),
                        'absolute_residual':mp.nstr(err,8),'scaled_residual':mp.nstr(scaled,8)})
        print(f'{name}: {mp.nstr(scaled,5)}',flush=True)
    L=mp.log(2*mp.pi); A=mp.euler+L
    def polylog_jets(z):
        # Five-point stencils avoid the tiny automatic differentiation step
        # at a resonant integer order. These remain numerical diagnostics.
        with mp.workdps(dps+40):
            h=mp.power(10,-max(10,math.ceil((dps+4)/4)))
            v={r:mp.polylog(2+r*h,z) for r in [-2,-1,0,1,2]}
            p1=(v[-2]-8*v[-1]+8*v[1]-v[2])/(12*h)
            p2=(-v[2]+16*v[1]-30*v[0]+16*v[-1]-v[-2])/(12*h*h)
            return [v[0],p1,p2]
    g=lambda t:mp.loggamma(t)-L/2
    zj=lambda j,s,x:mp.diff(lambda ss:mp.zeta(ss,x),s,j)
    for x in map(mp.mpf,['0.27','0.5','0.81']):
        h=x/2
        # Symmetric endpoint subtraction: stable digamma convolution.
        f=lambda t:-mp.digamma(t)
        fx=f(x)
        derivatives=[(-1)**j*(-mp.polygamma(j,x))/mp.factorial(j) for j in range(1,18)]
        def reg0(t):
            if t<x*mp.mpf('1e-5'):
                q=mp.polyval(list(reversed(derivatives)),t)
            else:q=(f(x-t)-fx)/t
            return q-mp.digamma(1+t)*f(x-t)
        c00=2*mp.quad(reg0,[0,h/4,h])+2*fx*mp.log(h)+mp.quad(lambda t:f(t)*f(1+x-t),[x,(1+x)/2,1])
        check(f'digamma_finite_part_x{x}',c00,2*mp.stieltjes(1,x)+mp.zeta(2))
        # Hadamard finite part of two trigammas: direct Taylor subtraction,
        # not the convolution formula under test.
        tri=lambda t:mp.polygamma(1,t)
        f0=tri(x); f1=mp.polygamma(2,x)
        cs=[(-1)**j*mp.polygamma(j+1,x)/mp.factorial(j) for j in range(2,18)]
        def reg1(t):
            if t<x*mp.mpf('1e-5'):
                q=mp.polyval(list(reversed(cs)),t)
            else:q=(tri(x-t)-f0+t*f1)/t**2
            return q+mp.polygamma(1,1+t)*tri(x-t)
        c11=2*mp.quad(reg1,[0,h/4,h])-2*f0/h-2*f1*mp.log(h)+mp.quad(lambda t:tri(t)*tri(1+x-t),[x,(1+x)/2,1])
        check(f'trigamma_finite_part_x{x}',c11,-4*zj(1,3,x)-2*mp.zeta(3,x))
        cc=mp.quad(lambda t:g(t)*g(x-t),[0,h,x])+mp.quad(lambda t:g(t)*g(1+x-t),[x,(1+x)/2,1])
        check(f'loggamma_convolution_x{x}',cc,zj(2,-1,x)+2*zj(1,-1,x)+(2-mp.zeta(2))*mp.zeta(-1,x))
    # Higher Stieltjes integrals use a rapidly convergent Taylor evaluator,
    # cross-checked against the independent generalized-Stieltjes routine.
    center=mp.mpf('1.5')
    degree=math.ceil((dps+10)/float(mp.log10(3)))
    coeff=[mp.stieltjes(1,center)]+[
        (-1)**(j+1)*(zj(1,j+1,center)+mp.harmonic(j)*mp.zeta(j+1,center))
        for j in range(1,degree+1)]
    reverse_coeff=list(reversed(coeff))
    def fast_gamma1(y):
        if y<1:
            return mp.log(y)/y+mp.polyval(reverse_coeff,y-mp.mpf('.5'))
        return mp.polyval(reverse_coeff,y-center)
    for y in map(mp.mpf,['.001','.25','.5','.81','1','1.5','1.999']):
        check(f'Stieltjes_Taylor_evaluator_y{y}',fast_gamma1(y),mp.stieltjes(1,y))
    for x in map(mp.mpf,['.27','.5','.81']):
        funcs=[lambda t:-mp.digamma(t),fast_gamma1]
        values=[f(x) for f in funcs]
        dc=[[mp.zeta(j+1,x) for j in range(1,18)],
            [-(zj(1,j+1,x)+mp.harmonic(j)*mp.zeta(j+1,x)) for j in range(1,18)]]
        def diff_quotient(n,t):
            if t<x*mp.mpf('1e-5'):
                return mp.polyval(list(reversed(dc[n])),t)
            return (funcs[n](x-t)-values[n])/t
        h=x/2
        for n,m in [(0,1),(1,1)]:
            def integrand(t):
                lt=mp.log(t)
                return (lt**n*diff_quotient(m,t)+lt**m*diff_quotient(n,t)
                    +funcs[n](1+t)*funcs[m](x-t)+funcs[m](1+t)*funcs[n](x-t))
            val=(mp.quad(integrand,[0,h/4,h])
                 +mp.quad(lambda t:funcs[n](t)*funcs[m](1+x-t),[x,(1+x)/2,1])
                 +values[m]*mp.log(h)**(n+1)/(n+1)+values[n]*mp.log(h)**(m+1)/(m+1))
            if n==0:
                target=mp.mpf('1.5')*mp.stieltjes(2,x)-mp.zeta(2)*values[0]-mp.zeta(3)
            else:
                target=(mp.stieltjes(3,x)-2*mp.zeta(2)*mp.stieltjes(1,x)
                        +2*mp.zeta(3)*values[0]+mp.zeta(4)/4)
            check(f'Stieltjes_convolution_C{n}{m}_x{x}',val,target)
    # Complex-order semigroup against ordinary quadrature.
    x=mp.mpf('0.37'); alpha=mp.mpc('1.4','0.2'); beta=mp.mpc('1.7','-0.3')
    R=lambda a,t:mp.zeta(1-a,t)/mp.gamma(a)
    conv=mp.quad(lambda t:R(alpha,t)*R(beta,x-t),[0,x/2,x])+mp.quad(lambda t:R(alpha,t)*R(beta,1+x-t),[x,(1+x)/2,1])
    check('complex_Hurwitz_semigroup',conv,R(alpha+beta,x))
    # Full shifted Gamma correlation, independent of the ordinary convolution.
    for x in map(mp.mpf,['0','0.5','0.37']):
        f=mp.loggamma
        if x==0: cc=mp.quad(lambda t:f(t)**2,[0,mp.mpf('.5'),1])
        else: cc=mp.quad(lambda t:f(t)*f(1+t-x),[0,x/2,x])+mp.quad(lambda t:f(t)*f(t-x),[x,(1+x)/2,1])
        z=-mp.mpf(1) if x==mp.mpf('.5') else mp.exp(2j*mp.pi*x)
        if x==0: p=[mp.diff(mp.zeta,2,j) for j in range(3)]
        else: p=polylog_jets(z)
        target=L**2/4+mp.re(p[2]-2*A*p[1]+(A**2+mp.pi**2/4)*p[0])/(2*mp.pi**2)
        check(f'shifted_gamma_correlation_x{x}',cc,target)
    # Parameter spectral derivatives at rational phase versus finite Hurwitz grid.
    p,q=2,5; z=mp.exp(2j*mp.pi*p/q)
    pj=polylog_jets(z)
    for j in range(3):
        lhs=pj[j]
        rhs=sum(mp.exp(2j*mp.pi*p*a/q)*sum(mp.binomial(j,r)*(-mp.log(q))**(j-r)*zj(r,2,mp.mpf(a)/q)
                     for r in range(j+1)) for a in range(1,q+1))/q**2
        check(f'cyclotomic_order_jet_{j}',lhs,rhs)
    # Fourier-mode test of the derivative contact term for G0.
    # Fp psi' paired against exp(-2*pi*i*x) is computed by local Taylor subtraction.
    w=2j*mp.pi
    # Divide exp(-wx)-1+wx by x^2, with its removable endpoint evaluated stably.
    def small(t):
        if abs(t)<mp.mpf('1e-6'):
            return sum((-w)**j*t**(j-2)/mp.factorial(j) for j in range(2,18))
        return (mp.exp(-w*t)-1+w*t)/t**2
    fp=mp.quad(lambda t:small(t)+mp.polygamma(1,1+t)*mp.exp(-w*t),[0,mp.mpf('.5'),1])-1
    check('derivative_contact_Fourier_mode',fp,w*(mp.euler+mp.log(w)-1))
    # The half-point identity is checked independently against the defining Stieltjes engine.
    l=mp.log(2)
    check('half_point_stieltjes',mp.stieltjes(1,mp.mpf('.5')),mp.stieltjes(1)-2*mp.euler*l-l*l)
    return {'status':'passed','decimal_precision':dps,'checks':results,
            'maximum_scaled_residual':mp.nstr(max(mp.mpf(r['scaled_residual']) for r in results),8),
            'scope':'floating-point diagnostics; no interval or equality certification'}


def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument('--exact-only',action='store_true');group.add_argument('--numeric-only',action='store_true')
    parser.add_argument('--dps',type=int,default=45)
    args=parser.parse_args()
    data={'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__}
    if not args.numeric_only:
        data['exact']=exact_suite()
        print('Exact assertions:',data['exact']['assertion_count'],flush=True)
    if not args.exact_only:data['numerical']=numeric_suite(args.dps)
    name='exact_results.json' if args.exact_only else 'numeric_results.json' if args.numeric_only else 'results.json'
    (OUT/name).write_text(json.dumps(data,indent=2)+'\n')
    print('Wrote',OUT/name)
if __name__=='__main__':main()
