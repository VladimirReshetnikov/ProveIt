#!/usr/bin/env python3
"""Floating-point diagnostics, NOT rigorous interval enclosures.

Nested and convergent-series evaluations share harmonic_em.py. Independent
mpmath Stieltjes/zeta calls check single letters. A five-point derivative
has a distinct discretization error. All these are diagnostics, not proofs.
"""
from pathlib import Path
from math import factorial
import json
import mpmath as mp
from harmonic_em import HarmonicEM
from verify_exact import compositions
X,Y,Z,Q,P=(1,0),(1,1),(1,2),(2,0),(2,1)

def features(E):
    R=E.R;A,B,C=R((Y,X,X)),R((X,Y,X)),R((X,X,Y))
    return dict(omega=R((X,Y))-R((Y,X)),omega2=R((X,Z))-R((Z,X)),
                D=A-C,theta=A-2*B+C,H=R((Q,X)),E=R((P,X))-R((Q,Y)))

def raw_ray(E,c):
    d=len(c);c=list(map(mp.mpf,c));out=mp.mpf(0)
    for j in range(1,d+1):
        r=d-j;denom=mp.mpf(1)
        for k in range(1,r+1):denom*=mp.fsum(c[:k])
        if not denom:raise ValueError('Ray lies on a polar divisor.')
        for ms in compositions(r,j):
            coefficient=(-1)**r/denom
            for slope,m in zip(c[r:],ms):coefficient*=slope**m/factorial(m)
            out+=coefficient*E.R(tuple((1,m) for m in ms))
    return out

def quartic(E,c):
    a=E.a;x=mp.stieltjes(0,a);y=mp.stieltjes(1,a);g2=mp.stieltjes(2,a);g3=mp.stieltjes(3,a)
    z=mp.zeta(2,a);zp=mp.diff(lambda s:mp.zeta(s,a),2);zpp=mp.diff(lambda s:mp.zeta(s,a),2,2)
    z3=mp.zeta(3,a);z3p=mp.diff(lambda s:mp.zeta(s,a),3);z4=mp.zeta(4,a)
    f=features(E);c1,c2,c3,c4=map(mp.mpf,c)
    C4=(x**4-6*x*x*z+3*z*z+8*x*z3-6*z4)/24
    T=y*(x*x-z)/2+x*zp-z3p
    quadratic=(c3*c3+c4*c4)*(x*g2-zpp)/4+(c4*c4-c3*c3)*f['omega2']/4+c3*c4*(y*y-zpp)/2
    return C4-((c2+c3+c4)*T/3+(c2-c4)*f['D']/2+(c2-2*c3+c4)*f['theta']/6)/c1+quadratic/(c1*(c1+c2))-c4**3*g3/(6*c1*(c1+c2)*(c1+c2+c3))

def main():
    mp.mp.dps=80;checks=[];values=[]
    def check(name,lhs,rhs,tolerance='1e-38'):
        error=abs(lhs-rhs);tol=mp.mpf(tolerance)
        checks.append(dict(name=name,absolute_residual=mp.nstr(error,10),tolerance=tolerance,pass_=bool(error<tol)))
        if not error<tol:raise AssertionError((name,mp.nstr(error,30),tolerance))
    for aval in ['0.5','1.0','1.5']:
        E=HarmonicEM(aval,64,40);low=HarmonicEM(aval,48,32)
        f=features(E);fl=features(low)
        values.append(dict(a=aval,**{name:mp.nstr(v,42) for name,v in f.items()}))
        for m in range(4):check(f'gamma[{m}] a={aval}',E.R(((1,m),)),mp.stieltjes(m,E.a))
        for k,m in [(2,0),(2,1),(2,2),(3,1)]:
            check(f'zeta letter ({k},{m}) a={aval}',E.R(((k,m),)),(-1)**m*mp.diff(lambda s:mp.zeta(s,E.a),k,m))
        for name in f:check(f'truncation stability {name} a={aval}',f[name],fl[name])
        for p,q in [(0,1),(0,2),(0,3),(1,2),(1,3)]:
            direct=E.R(((1,p),(1,q)))-E.R(((1,q),(1,p)))
            check(f'commutator series ({p},{q}) a={aval}',direct,E.commutator_series(p,q))
        check(f'curvature series a={aval}',f['theta'],E.xi_series()+mp.mpf('1.5')*E.R((Z,X))-E.R((Y,Y)))
        x=mp.stieltjes(0,E.a);y=mp.stieltjes(1,E.a);z=mp.zeta(2,E.a);p=-mp.diff(lambda s:mp.zeta(s,E.a),2)
        check(f'D stuffle bridge a={aval}',f['D'],-x*f['omega']/2+(x*p-y*z)/2-f['E'])
        for ray in [(1,1,1,1),(1,1,1,2),(1,1,2,3),(1,2,3,4),(2,-1,2,1)]:
            check(f'quartic ray {ray} a={aval}',raw_ray(E,ray),quartic(E,ray))
        shifted=HarmonicEM(E.a+1,64,40)
        check(f'commutator shift a={aval}',f['omega']-features(shifted)['omega'],(mp.log(E.a)*mp.stieltjes(0,E.a)-mp.stieltjes(1,E.a))/E.a)
    h=mp.mpf('1e-5');a=mp.mpf(1)
    def om(t):return features(HarmonicEM(t,64,40))['omega']
    derivative=(-om(a+2*h)+8*om(a+h)-8*om(a-h)+om(a-2*h))/(12*h)
    E=HarmonicEM(a,64,40);f=features(E);x=mp.stieltjes(0,a)
    bridge=x*mp.zeta(2,a)-mp.zeta(3,a)-2*f['H']-x*f['omega']-2*f['D']
    check('Gamma-weighted bridge, five-point derivative',derivative,bridge,'1e-17')
    check('Euler harmonic value H(1)=zeta(3)',f['H'],mp.zeta(3))
    report=dict(status='PASS',working_decimal_digits=80,settings=[dict(N=48,M=32),dict(N=64,M=40)],
                check_count=len(checks),values=values,checks=checks,
                scope='Floating-point regressions, not rigorous enclosures. Multiple nested evaluations share harmonic_em.py. Finite differences have a distinct truncation error.')
    target=Path(__file__).resolve().parents[1]/'data'/'numeric_checks.json'
    target.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
