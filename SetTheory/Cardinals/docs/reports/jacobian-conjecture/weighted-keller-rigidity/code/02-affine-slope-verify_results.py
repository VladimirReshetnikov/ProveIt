"""Reproduce finite exact checks accompanying the written all-degree proofs.

Run from the package root: python code/verify_results.py
These checks do not replace the polynomial/rational-function proofs.
"""
from __future__ import annotations
import json
import random
import sys
from pathlib import Path
import sympy as s
from weighted_keller import (t,v,x,y,z,weighted_jacobian,lift,normal_form,
                            classify,normalized_collision,infinitesimal_direction)

ROOT=Path(__file__).resolve().parents[1]
REPORT=[]

def check(name, fn):
    detail=fn()
    REPORT.append({'check':name,'status':'PASS','detail':detail})
    print('PASS:',name, flush=True)

def eq(a,b=0):
    assert s.cancel(s.expand(a-b))==0, (a,b)

def generic_coefficients():
    a,b,c,d,e,g=[s.Function(k)(t) for k in ['a','b','c','d','e','g']]
    J=weighted_jacobian(a*v+b,c*v+d,g*v+e)
    J0=(c*e+d*g)*s.diff(b,t)+2*b*(c*s.diff(e,t)-g*s.diff(d,t))-a*s.diff(d*e,t)
    J1=(c*e+d*g)*s.diff(a,t)+2*b*(c*s.diff(g,t)-g*s.diff(c,t)) \
       +a*(c*s.diff(e,t)-d*s.diff(g,t)-e*s.diff(c,t)-3*g*s.diff(d,t)) \
       +2*c*g*s.diff(b,t)
    J2=2*c*g*s.diff(a,t)-3*a*g*s.diff(c,t)+a*c*s.diff(g,t)
    eq(J,J0+v*J1+v*v*J2)
    return 'All three generic coefficient identities verified symbolically.'

def moving_coordinate():
    A,B,C,D=[s.Function(k)(t) for k in ['A','B','C','D']]
    J=weighted_jacobian(A*v+B,C*v+D,v)
    eq(J,(D*s.diff(B,t)-2*B*s.diff(D,t))
       +v*(D*s.diff(A,t)+2*C*s.diff(B,t)-3*A*s.diff(D,t)-2*B*s.diff(C,t))
       +v*v*(2*C*s.diff(A,t)-3*A*s.diff(C,t)))
    w,T,V=[s.Function(k)(t) for k in ['w','T','V']]
    k=s.symbols('k',nonzero=True)
    J1=s.expand((D*s.diff(A,t)+2*C*s.diff(B,t)-3*A*s.diff(D,t)-2*B*s.diff(C,t))
                .subs({A:w**3,C:k*w*w,B:w*w*T,D:w*V}).doit())
    eq(J1,w**4*(2*k*s.diff(T,t)-3*s.diff(V,t)))
    delta=s.symbols('delta')
    eq((D*s.diff(B,t)-2*B*s.diff(D,t)).subs({B:w*w*T,D:w*(2*k*T/3+delta)}).doit(),
       w**3*(delta-2*k*T/3)*s.diff(T,t))
    return 'Moving-coordinate and pole-equation reductions verified.'

def general_normal_form():
    beta,gamma=s.symbols('beta gamma',nonzero=True)
    E=s.Function('E')(t)
    U=1-2*beta*t/3; S=E+gamma*v
    p=(U**3*S-(U*U+U)/2)/gamma
    q=9/beta*(U*U*S-(2*U+1)/3)
    eq(weighted_jacobian(p,q,S),-1)
    return 'Jacobian -1 for symbolic nonzero beta,gamma and arbitrary E(t).'

def original_map():
    u=1+x*y; h=u*u*z+y*y*(1+3*u)
    F=(u*h,y+3*x*h,x*(5-3*u-x*x*z))
    eq(s.det(s.Matrix(F).jacobian([x,y,z])),-2)
    for pt in [(-1,1,5),(0,-2,-16)]:
        vals=[s.expand(f).subs(dict(zip((x,y,z),pt))) for f in F]
        assert vals==[0,-2,0]
    core=lift(*normal_form(1,1,1+t))
    sub={x:x,y:-s.Rational(2,3)*y,z:-2*z}
    for a,b,c in zip(core,F,[-s.Rational(1,2),-s.Rational(3,2),s.Rational(1,2)]):
        eq(a,c*b.subs(sub,simultaneous=True))
    return 'Original determinant, integral collision, and exact normalization verified.'

def diagonal_shear():
    cases=[(s.Rational(2),s.Rational(-3),1+t+t*t),
           (s.Rational(-1,2),s.Rational(4,3),t**3-2),
           (s.Rational(3,5),s.Rational(2,7),s.Integer(0))]
    star=lift(*normal_form(1,1,1+t))
    for beta,gamma,H in cases:
        E=1+beta*t+gamma*t*t*H
        actual=lift(*normal_form(beta,gamma,E))
        xyz={x:x,y:beta*y,z:gamma*(z+y*y*H.subs(t,x*y))}
        for a,b,scale in zip(actual,star,[1/gamma,1/beta,1]):
            eq(a,scale*b.subs(xyz,simultaneous=True))
    return 'Three rational scaling/shear cases checked exactly.'

def tame_inverse():
    lam=s.symbols('lam'); H=s.Function('H')
    X,Y,Z=s.symbols('X Y Z')
    P=z+y*y*H(x*y); F=(P,y+lam*x*P,x)
    xx=Z; yy=Y-lam*Z*X; zz=X-yy*yy*H(Z*yy)
    inverse=(xx,yy,zz)
    for expr,w in zip(inverse,(x,y,z)):
        eq(expr.subs(dict(zip((X,Y,Z),F)),simultaneous=True),w)
    for expr,w in zip(F,(X,Y,Z)):
        eq(expr.subs(dict(zip((x,y,z),inverse)),simultaneous=True),w)
    return 'Both inverse identities checked with an arbitrary symbolic H.'

def recognition_and_collisions():
    rng=random.Random(20260929)
    cases=0
    for n in range(18):
        beta=s.Rational(rng.choice([-3,-2,-1,1,2,3]),rng.choice([1,2,3]))
        gamma=s.Rational(rng.choice([-3,-2,-1,1,2,3]),rng.choice([1,2,3]))
        H=sum(s.Rational(rng.randint(-2,2))*t**j for j in range(n%5+1))
        ps=normal_form(beta,gamma,1+beta*t+gamma*t*t*H)
        scales=[s.Rational(rng.choice([-2,-1,1,2,3])) for _ in range(3)]
        ps=tuple(a*b for a,b in zip(ps,scales))
        result=classify(*ps)
        assert result.kind=='noninjective'
        eq(weighted_jacobian(*ps),-s.prod(scales))
        F=lift(*ps); p1,p2=normalized_collision(result)
        assert p1!=p2
        for f in F:
            eq(f.subs(dict(zip((x,y,z),p1))),f.subs(dict(zip((x,y,z),p2))))
        mutated=(ps[0]+t**2,ps[1],ps[2])
        assert classify(*mutated).kind=='not-keller'
        assert s.diff(weighted_jacobian(*mutated),t)!=0 or s.diff(weighted_jacobian(*mutated),v)!=0
        cases+=1
    for n in range(12):
        B=t*t*sum(s.Integer(rng.randint(-3,3))*t**j for j in range(n%6+1))
        lam=s.Integer(rng.randint(-3,3))
        assert classify(v+B,t+lam*(v+B),1).kind=='tame'
        eq(weighted_jacobian(v+B,t+lam*(v+B),1),-1)
    for ps in [(v,t,1+t*v),(v,t,1+v),(v,t,1+t)]:
        assert classify(*ps).kind=='not-keller'
    return {'seed':20260929,'noninjective_cases':cases,'mutations_rejected':cases,
            'tame_cases':12,'exceptional_rejections':3}

def degrees_and_support():
    base=lift(*normal_form(1,1,1+t))
    assert tuple(s.Poly(f,x,y,z).total_degree() for f in base)==(7,6,4)
    assert tuple(len(s.Poly(f,x,y,z).terms()) for f in base)==(7,6,3)
    degrees=[]
    for m in range(11):
        F=lift(*normal_form(1,1,1+t+t**(m+2)))
        found=tuple(s.Poly(f,x,y,z).total_degree() for f in F)
        assert found==(2*m+8,2*m+7,2*m+5)
        degrees.append({'shear_degree':m,'coordinate_degrees':found})
    return {'core_degrees':[7,6,4],'core_support':[7,6,3],'shears':degrees}

def first_order_and_obstruction():
    eps=s.symbols('eps')
    A,B,C,D,E,G,A2,B2,C2,D2,E2,G2=[s.Function(k)(t) for k in
                                  ['A','B','C','D','E','G','A2','B2','C2','D2','E2','G2']]
    # Coefficient formulas avoid expanding a needlessly large generic determinant.
    a=1+eps*A+eps**2*A2; b=eps*B+eps**2*B2
    c=eps*C+eps**2*C2; d=t+eps*D+eps**2*D2
    e=1+eps*E+eps**2*E2; g=eps*G+eps**2*G2
    J0=(c*e+d*g)*s.diff(b,t)+2*b*(c*s.diff(e,t)-g*s.diff(d,t))-a*s.diff(d*e,t)
    J1=(c*e+d*g)*s.diff(a,t)+2*b*(c*s.diff(g,t)-g*s.diff(c,t)) \
       +a*(c*s.diff(e,t)-d*s.diff(g,t)-e*s.diff(c,t)-3*g*s.diff(d,t)) \
       +2*c*g*s.diff(b,t)
    J2=2*c*g*s.diff(a,t)-3*a*g*s.diff(c,t)+a*c*s.diff(g,t)
    eq(s.expand(J0).coeff(eps,1),-(A+s.diff(D,t)+E+t*s.diff(E,t)))
    eq(s.expand(J1).coeff(eps,1),-(s.diff(C,t)+t*s.diff(G,t)+3*G))
    eq(s.expand(J2).coeff(eps,2),C*s.diff(G,t)-3*G*s.diff(C,t))
    P1,Q1,R1=[s.Function(k)(t,v) for k in ['P1','Q1','R1']]
    unrestricted=weighted_jacobian(v+eps*P1,t+eps*Q1,1+eps*R1)
    eq(unrestricted.coeff(eps,1),-s.diff(P1,v)-s.diff(Q1,t)-R1-t*s.diff(R1,t)-2*v*s.diff(R1,v))
    return ('Generic first-order equations, unrestricted linearization, and independence '
            'from ALL second-order affine-v corrections.')

def dual_numbers():
    eps=s.symbols('eps'); examples=[]
    for m in range(13):
        G=t**m; C,O=infinitesimal_direction(G)
        expected=s.Rational((m+3)*(2*m+3),m+1)*t**(2*m)
        eq(O,expected)
        eq(weighted_jacobian(v,t+eps*C*v,1+eps*G*v),-1+eps**2*O*v*v)
        I=s.integrate(O,(t,0,t))
        repaired=s.Poly(weighted_jacobian(v,t+eps*C*v+eps**2*I*v*v,1+eps*G*v)+1,eps)
        for j in range(3):
            eq(repaired.nth(j))
        examples.append({'m':m,'C':str(C),'obstruction':str(O),'quadratic_repair':str(I)})
    for G in [1+t+t**4,3-2*t**2+t**5,t**7-3*t+1]:
        C,O=infinitesimal_direction(G)
        eq(weighted_jacobian(v,t+eps*C*v,1+eps*G*v),-1+eps**2*O*v*v)
        m=s.degree(G,t); lc=s.Poly(G,t).LC()
        eq(s.Poly(O,t).LC(),s.Rational((m+3)*(2*m+3),m+1)*lc*lc)
    return {'monomial_examples':examples,'additional_mixed_polynomials':3}

def cubic_and_discriminant():
    P,Q,R,T=s.symbols('P Q R T')
    u=1+x*y; h=u*u*z+y*y*(1+3*u)
    F=(u*h,y+3*x*h,x*(5-3*u-x*x*z))
    f=R*T**3-2*T*T+Q*T-2*P
    tau=y+1/x
    sub={P:F[0],Q:F[1],R:F[2],T:tau}
    eq(f.subs(sub,simultaneous=True))
    eq(s.diff(f,T).subs(sub,simultaneous=True),2/x)
    eq(s.discriminant(f,T),4*(Q*Q-R*Q**3-16*P-27*R*R*P*P+18*P*Q*R))
    return 'Cubic elimination, inverse x-formula, and discriminant verified.'

def invalid_inputs():
    for ps in [(v**2,t,1),(v+1,t,1),(v,t+1,1),(s.sqrt(2)*v,t,1),(1/t,t,1)]:
        try:
            classify(*ps)
        except ValueError:
            pass
        else:
            raise AssertionError(f'Input should have raised ValueError: {ps}')
    assert classify(0,t,1).kind=='not-keller'
    return 'Domain and polynomiality validation tested; singular origin rejected.'

if __name__=='__main__':
    checks=[generic_coefficients,moving_coordinate,general_normal_form,original_map,
            diagonal_shear,tame_inverse,recognition_and_collisions,degrees_and_support,
            first_order_and_obstruction,dual_numbers,cubic_and_discriminant,invalid_inputs]
    for fn in checks:
        check(fn.__name__,fn)
    result={'python':sys.version.split()[0],'sympy':s.__version__,
            'repository_pin':'9b24a3a8d545af9624f6ac455f5b548be62818b6',
            'scope':'Exact finite symbolic checks, not a proof-assistant verification or a priority certificate.',
            'checks':REPORT}
    (ROOT/'data').mkdir(exist_ok=True)
    (ROOT/'data'/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    (ROOT/'data'/'verification.txt').write_text('\n'.join('PASS: '+r['check'] for r in REPORT)+'\n')
    print(f'{len(REPORT)} check groups passed.',flush=True)
