"""Exact symbolic identities and direct conditional-support regressions."""
from itertools import combinations
from math import prod
from random import Random
from pathlib import Path
import json
import sympy as S

def matching(masks):
    states={0}
    for mask in masks:
        states={used|1<<i for used in states for i in range(6) if mask>>i&1 and not used>>i&1}
    return bool(states)

def symbolic():
    n,p,q,x,y,z=S.symbols('n p q x y z')
    U=x+2*y+3*z;V=2*x+3*y+3*z;W=x+y+z
    A=(U**2-(V-2*U)**2/2)/3
    B=(W**2-(V-3*W)**2/3)/2
    c0=q+3*p+3*n+1;c1=q*U+p*V+n*W
    ps=[8*n*n+17*n*p+n*q+17*p*p+12*p*q-5*p+3*q*q-5*q,
        16*n*n+35*n*p-12*n*q+51*p*p+37*p*q-15*p+12*q*q-20*q,
        16*n*n+35*n*p-26*n*q+51*p*p+39*p*q-15*p+18*q*q-30*q,
        16*n*n+51*n*p-41*n*q+99*p*p+72*p*q-15*p+29*q*q-35*q,
        16*n*n+51*n*p-55*n*q+99*p*p+90*p*q-15*p+51*q*q-45*q,
        16*n*n+51*n*p-39*n*q+99*p*p+138*p*q-15*p+99*q*q-45*q]
    target=2*ps[0]*x*x+2*ps[1]*x*y+2*ps[2]*x*z+ps[3]*y*y+2*ps[4]*y*z+ps[5]*z*z
    if S.expand(2*(8*c1*c1-15*c0*(q*A+p*B))-target)!=0:raise RuntimeError('first gap identity')
    cone_constants=[]
    nn,pp,qq=S.symbols('nn pp qq')
    for poly,amount in zip(ps,[0,12,26,41,55,39]):
        remainder=S.Poly(S.expand((poly-amount*(p*p-n*q)).subs({n:nn+1,p:pp+1,q:qq+1})),nn,pp,qq)
        if min(remainder.coeffs())<0 or remainder.coeff_monomial(1)<=0:
            raise RuntimeError('coefficient positivity certificate')
        cone_constants.append(int(remainder.coeff_monomial(1)))
    u,v,w,a,b,t,s,h=S.symbols('u v w a b t s h')
    F=s**3+u*s*s*t+a*s*t*t+h*t**3+z*(3*s*s+v*s*t+b*t*t)+z*z*(3*s+w*t)/2+z**3/6
    H=S.hessian(S.diff(F,t),(s,t,z))
    schur=H.extract([0,2],[0,2])-H.extract([0,2],[1])*H.extract([1],[0,2])/(6*h)
    expected=S.Matrix([[a*a-3*u*h,a*b-S.Rational(3,2)*v*h],[a*b-S.Rational(3,2)*v*h,b*b-S.Rational(3,2)*w*h]])
    if any(S.simplify(c)!=0 for c in -3*h*schur/2-expected):raise RuntimeError('Hessian identity')
    Hs=S.hessian(S.diff(F,s),(s,t,z))
    ss=Hs.extract([1,2],[1,2])-Hs.extract([1,2],[0])*Hs.extract([0],[1,2])/6
    if S.expand(ss.det()-(2*(u*u-3*a)-(v-2*u)**2))!=0:
        raise RuntimeError('A upper bound identity')
    Hz=S.hessian(S.diff(F,z),(s,t,z))
    zz=Hz.extract([0,1],[0,1])-Hz.extract([0,1],[2])*Hz.extract([2],[0,1])
    if S.expand(zz.det()-(3*(w*w-2*b)-(v-3*w)**2))!=0:
        raise RuntimeError('B upper bound identity')
    return {'first_gap_six_coefficient_identity':True,'six_positive_cone_constants':cone_constants,'all_three_Hessian_identities':True}

def regressions():
    rng=Random(20261001);count=0
    while count<120:
        lm=[rng.randrange(1,8) for _ in range(rng.randrange(3,7))]
        rm=[rng.randrange(1,8) for _ in range(rng.randrange(3,7))]
        if not any(matching([lm[i] for i in I]) for I in combinations(range(len(lm)),3)):continue
        if not any(matching([rm[i] for i in I]) for I in combinations(range(len(rm)),3)):continue
        weights=[rng.randrange(1,8) for _ in rm]
        n=len(lm);p=sum(matching([lm[i] for i in I]) for I in combinations(range(n),2));q=sum(matching([lm[i] for i in I]) for I in combinations(range(n),3))
        W=sum(weights);U=sum(m.bit_count()*v for m,v in zip(rm,weights));V=sum((2 if m.bit_count()==1 else 3)*v for m,v in zip(rm,weights))
        B=sum(prod(weights[i] for i in I)*matching([rm[i] for i in I]) for I in combinations(range(len(rm)),2))
        A=sum(prod(weights[i] for i in I)*sum(matching([rm[i]&mask for i in I]) for mask in [3,5,6]) for I in combinations(range(len(rm)),2))
        T=sum(prod(weights[i] for i in I)*matching([rm[i] for i in I]) for I in combinations(range(len(rm)),3))
        expected=[q+3*p+3*n+1,q*U+p*V+n*W,q*A+p*B,q*T]
        actual=[]
        for j in range(4):
            val=0
            for J in combinations(range(len(rm)),j):
                wt=prod(weights[i] for i in J)
                for I in combinations(range(n+3),j+3):
                    masks=[]
                    for left in I:
                        if left<3:mask=7+sum(1<<(3+i) for i,k in enumerate(J) if rm[k]>>left&1)
                        else:mask=lm[left-3]
                        masks.append(mask)
                    if matching(masks):val+=wt
            actual.append(val)
        if actual!=expected:raise RuntimeError(('support identity',lm,rm,weights,actual,expected))
        if 8*actual[1]**2<=15*actual[0]*actual[2] or 5*actual[2]**2<=12*actual[1]*actual[3]:raise RuntimeError('gap failure')
        count+=1
    return {'direct_conditional_support_regressions':count,'all_gaps_strict':True}

if __name__=='__main__':
    result={**symbolic(),**regressions()}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
