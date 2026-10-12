#!/usr/bin/env python3
"""Exact algebra and independent diagnostics for the bilinear/kernel sections.

The exact cutoff tests use arbitrary initial values and rational recurrences;
they do not insert the claimed infinite sums. Numerical tests evaluate the
special functions directly and retain the exact upper endpoint. The primitive
is additionally compared with ordinary quadrature of its asserted derivative.
These floating-point diagnostics are not interval certificates.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as F
from pathlib import Path
import sympy as s

OUT = Path(__file__).resolve().parent


def exact_checks():
    z, a, b, rho, alpha, beta, t = s.symbols('z a b rho alpha beta t', nonzero=True)
    h = (z+a)/(z+b)
    Q = (z+b)*(z+b+1)
    P = rho*Q*h*h.subs(z,z+1)
    A = Q*h
    B = -t*beta*Q*h.subs(z,z+1)
    linear1 = beta*A.subs(z,z+1)/Q.subs(z,z+1)+B/(t*Q)
    linear2 = (alpha*B.subs(z,z+1)/P.subs(z,z+1)+A/(t*P)).subs(alpha,1/(t*t*beta))
    assert s.cancel(linear1)==0 and s.cancel(linear2)==0
    checks = {'symbolic_linear_cancellations': 2}

    # Both equal-degree and unequal-degree denominators, arbitrary seeds.
    finite = 0
    for aa,bb in [(F(1,2),F(3,2)),(F(2,3),F(7,4))]:
      for unequal in [False,True]:
        q = lambda k: (k+bb)*(k+bb+1)
        hh = (lambda k: k+aa) if unequal else (lambda k:(k+aa)/(k+bb))
        p = lambda k:q(k)*hh(k)*hh(k+1)
        for al,be,base_t in [(F(-1),F(-1),F(1)),(F(1,2),F(1,8),F(4))]:
          for tt in [base_t,-base_t]:
            A0 = lambda k:q(k)*hh(k)
            B0 = lambda k:-tt*be*q(k)*hh(k+1)
            C0 = lambda k:A0(k)+B0(k)
            E=[F(7,11)]; G=[F(-4,9)]
            for k in range(1,10):
                E.append(E[-1]-al**k/p(k)); G.append(G[-1]-be**k/q(k))
            endpoint=be*hh(1)*E[0]-G[0]/(tt*hh(1))-C0(0)*E[0]*G[0]/tt
            total=F(0)
            for n in range(9):
                total+=tt**n*(C0(n+1)-C0(n)/tt)*E[n]*G[n]
                top=tt**n*(A0(n+1)*E[n]*G[n+1]+B0(n+1)*E[n+1]*G[n])
                assert total==endpoint+top,(aa,bb,unequal,al,tt,n)
                finite+=1
    checks['rational_bilinear_cutoffs']=finite

    # Reconstruct all small divisor strings satisfying the orbit condition.
    from itertools import product
    divisor=0; compatible=0
    for rs in product(range(-2,3),repeat=5):
        hs=[0]*6
        for j in range(4,-1,-1): hs[j]=rs[j]-hs[j+1]
        test=sum((-1)**j*rs[j] for j in range(5))==0
        assert (hs[0]==0)==test
        assert all(hs[j]+hs[j+1]==rs[j] for j in range(5))
        divisor+=1;compatible+=int(test)
    checks['divisor_strings']=divisor
    checks['compatible_divisor_strings']=compatible

    cutoff=0
    for zz,ww in [(F(1,2),F(1)),(F(1),F(2)),(F(7,10),F(13,10))]:
      u=[F(5,7)];v=[F(11,13)]
      for n in range(12):
        u.append(1/((zz+n)*(zz+n+1))-u[-1])
        v.append(1/((ww+n)*(ww+n+1))-v[-1])
      K=zz*u[0]/(2*ww)+ww*v[0]/(2*zz)-(zz*ww-(zz+ww)/2)*u[0]*v[0]
      S=u[0]*v[0]/2+(zz*zz*u[0]-ww*ww*v[0])/(2*zz*ww*(zz-ww))
      totalK=F(0);totalS=F(0)
      for n in range(12):
        totalK+=(2*n+zz+ww)*u[n]*v[n]
        totalS+=(-1)**n*u[n]*v[n]
        r1=(n+zz)*(n+ww+1)*u[n]*v[n+1]
        r2=(n+zz+1)*(n+ww)*u[n+1]*v[n]
        assert totalK==K-(r1+r2)/2
        assert totalS==S+(-1)**n*(-r1+r2)/(2*(zz-ww))
        cutoff+=2
    checks['rational_kernel_cutoffs']=cutoff

    fs=s.symbols('f0:3');bs=s.symbols('b0:3')
    matrix=s.Matrix(3,3,lambda i,j:fs[i]*bs[j]+bs[i]*fs[j]-fs[i]*fs[j])
    assert s.expand(matrix.det())==0
    assert s.expand(matrix[:2,:2].det()+(fs[0]*bs[1]-bs[0]*fs[1])**2)==0
    checks['rank_determinant_identities']=2
    L,pi=s.symbols('L pi')
    uu=2*L-1;vv=s.Rational(3,2)-2*L
    expr=s.Rational(1,4)*uu+vv-s.Rational(1,2)*uu*vv
    assert s.expand(expr-2*(1-L)**2)==0
    expr=(pi-2)/4+uu-(s.Rational(1,2)-s.Rational(3,4))*(pi-2)*uu
    assert s.expand(2*expr-((pi+2)*L-2))==0
    assert s.expand(uu**2/2+uu+(1-pi**2/6)/2-(2*L**2-pi**2/12))==0
    # r=s=1: f'=U+zU', B'=pi^2*(-1)/12 at z=1.
    fp=uu+1-pi**2/6;bp=-pi**2/12
    assert s.expand(2*fp*bp-fp**2-(pi**2*L/3-4*L**2))==0
    checks['printed_evaluations']=4
    result={'all_passed':True,'arithmetic':'exact rational / symbolic polynomial',**checks}
    (OUT/'kernel_exact.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


def numerical_checks():
    import mpmath as mp
    mp.mp.dps=50
    records=[]
    def fmt(x):return mp.nstr(x,52)
    def record(name,lhs,rhs):
        err=abs(lhs-rhs)
        assert err<mp.mpf('1e-43')*(1+abs(rhs)),(name,err)
        records.append({'test':name,'lhs':fmt(lhs),'rhs':fmt(rhs),'abs_error':fmt(err)})
    def U(z):return mp.digamma((z+1)/2)-mp.digamma(z/2)-1/z
    def Ud(z,r):return (mp.polygamma(r,(z+1)/2)-mp.polygamma(r,z/2))/2**r+(-1)**(r+1)*mp.factorial(r)/z**(r+1)
    def K(z,w):return z*U(z)/(2*w)+w*U(w)/(2*z)-(z*w-(z+w)/2)*U(z)*U(w)
    def S(z,w):return U(z)*U(w)/2+(z*z*U(z)-w*w*U(w))/(2*z*w*(z-w))
    for z in [mp.mpf('.5'),mp.mpf('1.3'),mp.mpc('.7','.2')]:
      for r in range(3):
        integral=mp.quad(lambda y:mp.exp(-z*y)*(-y)**r*mp.tanh(y/2),[0,1,mp.inf])
        record(f'U derivative integral z={z} r={r}',Ud(z,r),integral)
    for z,w in [(mp.mpf('.5'),mp.mpf(1)),(mp.mpf(1),mp.mpf(2)),(mp.mpc('.7','.2'),mp.mpc('1.3','-.1'))]:
        n=17
        r1=(n+z)*(n+w+1)*U(n+z)*U(n+w+1)
        r2=(n+z+1)*(n+w)*U(n+z+1)*U(n+w)
        record(f'K cutoff z={z} w={w}',mp.fsum((2*j+z+w)*U(j+z)*U(j+w) for j in range(n+1)),K(z,w)-(r1+r2)/2)
        record(f'S cutoff z={z} w={w}',mp.fsum((-1)**j*U(j+z)*U(j+w) for j in range(n+1)),S(z,w)+(-1)**n*(-r1+r2)/(2*(z-w)))
    for d,theta in [(2,mp.pi/2),(3,mp.pi/3)]:
        al=mp.exp(1j*theta);be=mp.conj(al);n=23
        e0=mp.polylog(d,al);E=[e0]
        for k in range(1,n+2):E.append(E[-1]-al**k/k**d)
        lhs=mp.fsum(((j+1)**d-j**d)*abs(E[j])**2 for j in range(n+1))
        endpoint=mp.cot(theta/2)*mp.im(e0)-mp.re(e0)
        top=(n+1)**d*(E[n]*mp.conj(E[n+1])-be*E[n+1]*mp.conj(E[n]))/(1-be)
        record(f'Hermitian d={d}',lhs,endpoint+top)
    def LL(z):return mp.loggamma((z+1)/2)-mp.loggamma(z/2)
    def QQ(z):return 2*z*LL(z)-4*(mp.diff(lambda s:mp.zeta(s,(z+1)/2),-1)-mp.diff(lambda s:mp.zeta(s,z/2),-1))
    def UU(z):return 2*LL(z)-mp.log(z)
    z0=mp.mpf('.7');z=mp.mpf('1.4')
    record('Gamma primitive Q',QQ(z)-QQ(z0),mp.quad(lambda x:x*U(x),[z0,z]))
    record('Gamma primitive L',LL(z)-LL(z0),mp.quad(lambda x:(U(x)+1/x)/2,[z0,z]))
    record('Gamma primitive U',UU(z)-UU(z0),mp.quad(U,[z0,z]))
    w0=mp.mpf('1.1');w=mp.mpf('1.8');n=6
    dqz=[QQ(j+z)-QQ(j+z0) for j in range(n+2)]
    dqw=[QQ(j+w)-QQ(j+w0) for j in range(n+2)]
    duz=[UU(j+z)-UU(j+z0) for j in range(n+1)]
    duw=[UU(j+w)-UU(j+w0) for j in range(n+1)]
    rhs=dqz[0]*(LL(w)-LL(w0))+(LL(z)-LL(z0))*dqw[0]-dqz[0]*dqw[0]
    rhs-=(dqz[n]*dqw[n+1]+dqz[n+1]*dqw[n])/2
    lhs=mp.fsum(dqz[j]*duw[j]+duz[j]*dqw[j] for j in range(n+1))
    record('Rectangular Gamma-Hurwitz finite cutoff',lhs,rhs)
    result={'all_passed':True,'working_decimal_digits':50,'interval_certification':False,'test_count':len(records),'max_abs_error':fmt(max(mp.mpf(r['abs_error']) for r in records)),'tests':records}
    (OUT/'kernel_numeric.json').write_text(json.dumps(result,indent=2)+'\n')
    return {k:v for k,v in result.items() if k!='tests'}


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--exact-only',action='store_true')
    args=parser.parse_args()
    print(json.dumps(exact_checks(),indent=2))
    if not args.exact_only:print(json.dumps(numerical_checks(),indent=2))
