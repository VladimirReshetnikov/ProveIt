#!/usr/bin/env python3
"""Reproducible algebra and numerical audits for global_fueter_inversion.tex.

Dependencies: Python 3.10+, sympy, mpmath.
Run: python verify_results.py --output verification_results.json
These checks audit formulas; they are not substitutes for the proofs.
"""
from __future__ import annotations
import argparse
import json
import platform
from pathlib import Path
import sympy as s
import mpmath as mp


def symbolic_checks() -> list[dict[str, object]]:
    x, y, u, v = s.symbols('x y u v', real=True)
    X, Y = x-u, y-v
    R2 = X**2 + Y**2
    L = s.log(R2)/2
    theta = s.Function('theta')(x,y)
    rules = {s.diff(theta,x): -Y/R2, s.diff(theta,y): X/R2}
    h0A, h0B = theta/(2*s.pi), -L/(2*s.pi)
    stems = [(h0A,h0B), ((x*theta+y*L)/(2*s.pi), (y*theta-x*L)/(2*s.pi))]
    kernels = [(X/(s.pi*y*R2), -Y/(s.pi*y*R2)+L/(s.pi*y**2)),
               ((x*X+y*Y)/(s.pi*y*R2)+L/(s.pi*y),
                X/(s.pi*R2)-x*Y/(s.pi*y*R2)+x*L/(s.pi*y**2))]
    checks: list[dict[str,object]]=[]
    def check(name: str, expr: s.Expr) -> None:
        value=s.simplify(s.expand(expr.doit()).subs(rules))
        passed=value==0
        checks.append({'name':name,'passed':passed,'residual':str(value)})
        if not passed:
            raise AssertionError(f'{name}: {value}')
    for k,((A,B),(P,Q)) in enumerate(zip(stems,kernels)):
        check(f'K{k}: stem Cauchy-Riemann x',s.diff(A,x)-s.diff(B,y))
        check(f'K{k}: stem Cauchy-Riemann y',s.diff(A,y)+s.diff(B,x))
        check(f'K{k}: displayed P',2*s.diff(A,y)/y-P)
        check(f'K{k}: displayed Q',2*s.diff(B,y)/y-2*B/y**2-Q)
        check(f'K{k}: Vekua 1',s.diff(P,x)-s.diff(Q,y)-2*Q/y)
        check(f'K{k}: Vekua 2',s.diff(Q,x)+s.diff(P,y))
        C,H=B/y,A-x*B/y
        for label,expr in [('dC/dx',s.diff(C,x)+P/2),('dC/dy',s.diff(C,y)-Q/2),
                           ('dH/dx',s.diff(H,x)-(x*P+y*Q)/2),
                           ('dH/dy',s.diff(H,y)-(y*P-x*Q)/2)]:
            check(f'K{k}: {label}',expr)
        W=-(P+y*s.diff(P,y)+s.I*y*s.diff(P,x))/2
        z,p=x+s.I*y,u+s.I*v
        expected=(-1/(z-p)**2 if k==0 else 1/(z-p)-p/(z-p)**2)/(2*s.pi*s.I)
        check(f'K{k}: holomorphic detector',W-expected)
    return checks


def kernel(x: mp.mpf, y: mp.mpf, p: mp.mpc, degree: int) -> tuple[mp.mpf,mp.mpf]:
    if y==0:
        raise ValueError('Unpaired kernels are evaluated only off the real axis.')
    X,Y=x-p.real,y-p.imag
    R2=X*X+Y*Y
    if R2==0:
        raise ValueError('Cannot evaluate at the kernel singularity.')
    L=mp.log(R2)/2
    if degree==0:
        return X/(mp.pi*y*R2), -Y/(mp.pi*y*R2)+L/(mp.pi*y*y)
    if degree==1:
        return (x*X+y*Y)/(mp.pi*y*R2)+L/(mp.pi*y), X/(mp.pi*R2)-x*Y/(mp.pi*y*R2)+x*L/(mp.pi*y*y)
    raise ValueError('degree must be 0 or 1')


def periods(p:mp.mpc,center:mp.mpc,radius:mp.mpf,degree:int,paired:bool=False) -> tuple[mp.mpf,mp.mpf]:
    def integrand(t:mp.mpf,index:int)->mp.mpf:
        x,y=center.real+radius*mp.cos(t),center.imag+radius*mp.sin(t)
        dx,dy=-radius*mp.sin(t),radius*mp.cos(t)
        P,Q=kernel(x,y,p,degree)
        if paired:
            Pm,Qm=kernel(x,y,p.conjugate(),degree)
            P,Q=P-Pm,Q-Qm
        return (-P*dx+Q*dy)/2 if index==0 else ((x*P+y*Q)*dx+(y*P-x*Q)*dy)/2
    parts=[j*mp.pi/2 for j in range(5)]
    return tuple(mp.quad(lambda t:integrand(t,k),parts) for k in (0,1))



def quaternion_symbolic_checks()->list[dict[str,object]]:
    """Audit moments with generic, noncommuting right quaternion coefficients.

    Six coordinate units form a spherical 2-design, so their equal-weight
    average gives exact averages for the linear/quadratic polynomials used.
    """
    u,v=s.symbols('u v',real=True,nonzero=True)
    a=list(s.symbols('a0:4',real=True)); b=list(s.symbols('b0:4',real=True))
    def mul(p,q):
        return [p[0]*q[0]-sum(p[j]*q[j] for j in (1,2,3)),
                p[0]*q[1]+p[1]*q[0]+p[2]*q[3]-p[3]*q[2],
                p[0]*q[2]-p[1]*q[3]+p[2]*q[0]+p[3]*q[1],
                p[0]*q[3]+p[1]*q[2]-p[2]*q[1]+p[3]*q[0]]
    vals=[]; first=[]; squared=[]
    for axis in (1,2,3):
        for sign in (-1,1):
            q=[u,s.Integer(0),s.Integer(0),s.Integer(0)];q[axis]=sign*v
            amp=[r+b[j] for j,r in enumerate(mul(q,a))]
            dens=[2*r/v for r in amp]
            w=q.copy();w[0]=s.Integer(0)
            vals.append(dens);first.append(mul(w,dens))
            squared.append(sum(r*r for r in amp))
    checks=[]
    def check(name,expr):
        val=s.expand(expr)
        if val!=0: raise AssertionError(f'{name}: {val}')
        checks.append({'name':name,'passed':True,'residual':'0'})
    for j in range(4):
        check(f'generic quaternion zeroth moment component {j}',
              sum(row[j] for row in vals)/6-2*(u*a[j]+b[j])/v)
        check(f'generic quaternion first moment component {j}',
              sum(row[j] for row in first)/6+2*v*a[j])
    check('generic quaternion critical energy norm',sum(squared)/6-
          sum((u*a[j]+b[j])**2+v*v*a[j]**2 for j in range(4)))
    return checks


def numerical_checks()->list[dict[str,object]]:
    mp.mp.dps=50
    p=mp.mpc('1.2','2.0'); radius=mp.mpf('0.37')
    checks=[]
    tests=[('unpaired enclosing',p,False,1),('unpaired nonenclosing',p+1,False,0),
           ('paired upper',p,True,1),('paired lower',p.conjugate(),True,-1)]
    for name,center,paired,winding in tests:
        for k in (0,1):
            val=periods(p,center,radius,k,paired)
            expected=(winding,0) if k==1 else (0,winding)
            err=max(abs(val[j]-expected[j]) for j in (0,1))
            passed=err<mp.mpf('1e-42')
            checks.append({'name':f'{name} K{k}','periods':[mp.nstr(w,48) for w in val],
                           'expected':expected,'max_error':mp.nstr(err,8),'passed':bool(passed)})
            if not passed: raise AssertionError(checks[-1])
    # A normal-circle flux audit, at I=i, with scalar a,b. Quaternions in
    # C_i are represented by mpc; right-H-linearity extends the identity.
    # Integrate the actual tubular surface factor y^2*rho, then divide by
    # v^2 to obtain density per unit area of the limiting sphere.
    a,b=mp.mpf('0.7'),mp.mpf('-0.4')
    expected=2/p.imag*(p*a+b)
    for rho in [mp.mpf('0.2'),mp.mpf('0.1'),mp.mpf('0.05'),mp.mpf('0.025')]:
        def flux(t):
            x=p.real+rho*mp.cos(t);y=p.imag+rho*mp.sin(t)
            P0,Q0=kernel(x,y,p,0);P1,Q1=kernel(x,y,p,1)
            gv=mp.mpc(P1*a+P0*b,Q1*a+Q0*b)
            normal=mp.mpc(mp.cos(t),mp.sin(t))
            return normal*gv*y*y*rho/(p.imag*p.imag)
        value=mp.quad(flux,[j*mp.pi/2 for j in range(5)])
        err=abs(value-expected)
        # Only convergence is expected: spherical direction I is held fixed.
        checks.append({'name':f'normal flux rho={rho}','value':[mp.nstr(value.real,25),mp.nstr(value.imag,25)],
                       'limiting_density':[mp.nstr(expected.real,25),mp.nstr(expected.imag,25)],
                       'absolute_error':mp.nstr(err,12),'passed':bool(err<3*rho)})
        if err>=3*rho: raise AssertionError(checks[-1])
    errors=[mp.mpf(c['absolute_error']) for c in checks[-4:]]
    if not all(errors[j+1]<errors[j] for j in range(3)):
        raise AssertionError('Normal-circle flux errors did not decrease.')
    # Full spherical average of |P+I Q|^2 is |P|^2+|Q|^2.
    # Audit the logarithmic energy coefficient using genuinely quaternionic
    # right coefficients and numerical integration over the normal angle.
    qa=[mp.mpf(z) for z in ('0.7','0.2','-0.3','0.4')]
    qb=[mp.mpf(z) for z in ('-0.4','0.5','0.1','-0.2')]
    target=8*sum((p.real*qa[j]+qb[j])**2+p.imag**2*qa[j]**2 for j in range(4))
    energy_errors=[]
    for rho in [mp.mpf('0.025'),mp.mpf('0.0125'),mp.mpf('0.00625'),mp.mpf('0.003125')]:
        def density(t):
            x=p.real+rho*mp.cos(t); y=p.imag+rho*mp.sin(t)
            P0,Q0=kernel(x,y,p,0); P1,Q1=kernel(x,y,p,1)
            norm2=sum((P1*qa[j]+P0*qb[j])**2+(Q1*qa[j]+Q0*qb[j])**2 for j in range(4))
            return 4*mp.pi*y*y*rho*rho*norm2
        val=mp.quad(density,[j*mp.pi/2 for j in range(5)])
        error=abs(val-target);energy_errors.append(error)
        passed=error<2*rho
        checks.append({'name':f'critical energy slope rho={rho}',
                       'value':mp.nstr(val,30),'limit':mp.nstr(target,30),
                       'absolute_error':mp.nstr(error,12),'passed':bool(passed)})
        if not passed: raise AssertionError(checks[-1])
    if not all(energy_errors[j+1]<energy_errors[j] for j in range(3)):
        raise AssertionError('Critical energy slope errors did not decrease.')
    return checks


def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('verification_results.json'))
    args=parser.parse_args()
    symbolic=symbolic_checks()+quaternion_symbolic_checks();numerical=numerical_checks()
    result={'python':platform.python_version(),'sympy':s.__version__,'mpmath':mp.__version__,
            'precision_decimal_digits':mp.mp.dps,'symbolic':symbolic,'numerical':numerical,
            'all_passed':all(c['passed'] for c in symbolic+numerical),
            'scope':'Formula audits and numerical checks, not a formal proof or a priority certification.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(f'{len(symbolic)} symbolic checks and {len(numerical)} numerical checks passed.')
    print(f'Report: {args.output.resolve()}')

if __name__=='__main__':
    main()
