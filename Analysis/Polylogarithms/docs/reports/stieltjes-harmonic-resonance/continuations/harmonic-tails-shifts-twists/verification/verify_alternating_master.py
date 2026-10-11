#!/usr/bin/env python3
"""Replay exact finite-weight algebra and optional independent numeric checks.

The exact audit treats zeta values and log(2) as formal generators. It
expands the displayed two-variable closed form as a Laurent polynomial,
checks cancellation of every apparent axial pole, and independently
compares its coefficients with the finite-cutoff plus odd-parity formula.
No integer-relation search is used. The all-order proof is in the article;
this audit is a finite consistency check, not a replacement for that proof.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as sp

LOG2 = sp.Symbol('log2')

def one_value(order: int, sign: int, formal_T=sp.Integer(0)):
    if order == 1:
        return formal_T if sign == 1 else -LOG2
    coefficient = sp.Integer(1) if sign == 1 else sp.Rational(2)**(1-order)-1
    return coefficient*sp.Symbol(f'zeta{order}')

def choose(n: int, k: int):
    return sp.binomial(n,k) if 0 <= k <= n else sp.Integer(0)

def parity_value(p: int, q: int, alpha: int, beta: int, formal_T=sp.Integer(0)):
    assert p >= 2 and q >= 1 and (p+q)%2 == 1
    weight = p+q
    L=lambda r,sign:one_value(r,sign,formal_T)
    def mu(r):
        return (-1)**p*(choose(r-1,p-1)*L(r,alpha)
                       +choose(r-1,q-1)*L(r,beta))
    value = (-L(weight,alpha*beta)
             +(1+(-1)**p)*L(p,alpha)*L(q,beta)
             +mu(weight))/2
    value -= sum(L(2*k,alpha*beta)*mu(weight-2*k)
                 for k in range(1,(weight+1)//2))
    return sp.expand(value)

def exact_moment(p: int, q: int, d: int, alpha: int, beta: int):
    assert p >= 2 and q >= 2 and 1 <= d < min(p,q)
    assert d%2 == 1 and (p+q)%2 == 0
    return sp.expand(-parity_value(p,q-d,alpha,-beta)
                     -parity_value(q,p-d,beta,-alpha)
                     -one_value(p+q-d,-alpha*beta))

def add(*polynomials):
    out = {}
    for poly in polynomials:
        for exponent,coefficient in poly.items():
            out[exponent] = out.get(exponent,0)+coefficient
    return {e:sp.expand(c) for e,c in out.items() if sp.expand(c)!=0}

def scale(poly,factor):
    return {e:factor*c for e,c in poly.items()}

def shift(poly,dx,dy):
    return {(i+dx,j+dy):c for (i,j),c in poly.items()}

def product(first,second,max_degree):
    out = {}
    for (i,j),a in first.items():
        for (k,l),b in second.items():
            if i+j+k+l <= max_degree:
                out[(i+k,j+l)] = out.get((i+k,j+l),0)+a*b
    return {e:sp.expand(c) for e,c in out.items() if sp.expand(c)!=0}

def O_axis(sign,axis,max_half_degree):
    return {(2*j if axis==0 else 0,2*j if axis==1 else 0):one_value(2*j+1,sign)
            for j in range(max_half_degree+1)}

def O_diagonal(sign,orientation,max_half_degree):
    # Independently expand O(x+y) or O(x-y) by the binomial theorem.
    out={}
    for j in range(max_half_degree+1):
        for ix in range(2*j+1):
            iy=2*j-ix
            out[(ix,iy)]=one_value(2*j+1,sign)*choose(2*j,ix)*orientation**iy
    return out

def C_axis(sign,axis,max_half_degree):
    # C=pi R/2=1/(2t)-sum Li_(2k)(sign)t^(2k-1).
    out={(-1,0) if axis==0 else (0,-1):sp.Rational(1,2)}
    for k in range(1,max_half_degree+1):
        out[(2*k-1,0) if axis==0 else (0,2*k-1)]=-one_value(2*k,sign)
    return out

def closed_master(alpha,beta,total_order):
    degree=total_order-4
    half=total_order//2-1
    c=-alpha*beta
    def U(sign):
        return scale(shift(add(O_diagonal(sign,1,half),
                               scale(O_diagonal(sign,-1,half),-1)),-1,-1),
                     sp.Rational(1,2))
    def V(sign):
        return scale(add(O_diagonal(sign,1,half),O_diagonal(sign,-1,half)),
                     sp.Rational(1,2))
    cx=C_axis(c,0,half); cy=C_axis(c,1,half)
    terms=[
        product(shift(C_axis(alpha,0,half),-1,0),O_axis(-beta,1,half),degree),
        product(shift(C_axis(beta,1,half),0,-1),O_axis(-alpha,0,half),degree),
        scale(product(shift(cy,0,1),U(alpha),degree),-1),
        scale(product(shift(cx,1,0),U(beta),degree),-1),
        scale(product(shift(cx,-1,0),V(-beta),degree),-1),
        scale(product(shift(cy,0,-1),V(-alpha),degree),-1)]
    return add(*terms)

def exact_audit(total_order=18):
    checked=[]
    for alpha,beta in [(1,1),(1,-1),(-1,1),(-1,-1)]:
        polynomial=closed_master(alpha,beta,total_order)
        negative=[str(e) for e in polynomial if min(e)<0]
        odd=[str(e) for e in polynomial if e[0]%2 or e[1]%2]
        assert not negative,negative
        assert not odd,odd
        for p in range(2,total_order,2):
            for q in range(2,total_order-p+1,2):
                observed=polynomial.get((p-2,q-2),0)
                expected=exact_moment(p,q,1,alpha,beta)
                assert sp.expand(observed-expected)==0,(p,q,alpha,beta)
                checked.append({'p':p,'q':q,'alpha':alpha,'beta':beta,
                                'value':str(expected)})
    # Check the simple diagonal convolution separately.
    diagonal=[]
    for m in range(2,total_order//2+1):
        lhs=sum(exact_moment(2*a,2*m-2*a,1,-1,-1) for a in range(1,m))
        rhs=one_value(2*m-1,1)/2-sum(one_value(2*j,-1)*one_value(2*m-2*j-1,1)
                                             for j in range(1,m-1))
        assert sp.expand(lhs-rhs)==0,m
        diagonal.append(m)
    # Retain T instead of 0 and verify its cancellation in all admissible
    # endpoint parity rows. This check is independent of the chosen values.
    formal_T=[]
    T=sp.Symbol('T')
    for weight in range(3,total_order,2):
        for p in range(2,weight):
            q=weight-p
            for alpha,beta in [(1,1),(1,-1),(-1,1),(-1,-1)]:
                value=parity_value(p,q,alpha,beta,T)
                assert sp.diff(value,T)==0,(p,q,alpha,beta,value)
                formal_T.append({'p':p,'q':q,'alpha':alpha,'beta':beta})
    return {'status':'passed','arithmetic':'exact symbolic rational arithmetic',
            'maximum_p_plus_q':total_order,'coefficients_checked':len(checked),
            'axial_laurent_poles_remaining':0,'odd_powers_remaining':0,
            'regularization_cancellations_checked':len(formal_T),
            'diagonal_convolutions_checked':diagonal,
            'coefficient_values':checked,
            'scope':'finite algebra audit; analytic proof and all-order derivation are in article'}

def numeric_audit():
    import mpmath as mp
    mp.mp.dps=55
    def op(x):
        return -(mp.digamma(1+x)+mp.digamma(1-x)+2*mp.euler)/2
    def odd(sign,x):
        return op(x) if sign==1 else -mp.log(2)+op(x/2)-op(x)
    def trig(sign,x):
        return mp.cot(mp.pi*x) if sign==1 else mp.csc(mp.pi*x)
    def B(v):
        return (mp.digamma((v+1)/2)-mp.digamma(v/2))/2
    def tail(n,sign,x):
        if x==0:
            return (mp.zeta(2,n+1) if sign==1 else
                    (-1)**(int(n)+1)*(mp.zeta(2,(n+1)/2)-mp.zeta(2,(n+2)/2))/4)
        if sign==1:
            return (mp.digamma(n+1+x)-mp.digamma(n+1-x))/(2*x)
        return (-1)**(int(n)+1)*(B(n+1-x)-B(n+1+x))/(2*x)
    def rhs(a,b,x,y):
        c=-a*b
        U=lambda s:(odd(s,x+y)-odd(s,x-y))/(2*x*y)
        V=lambda s:(odd(s,x+y)+odd(s,x-y))/2
        return mp.pi/2*(trig(a,x)*odd(-b,y)/x+trig(b,y)*odd(-a,x)/y
                 -y*trig(c,y)*U(a)-x*trig(c,x)*U(b)
                 -trig(c,x)*V(-b)/x-trig(c,y)*V(-a)/y)
    def lhs(a,b,x,y):
        f=lambda n:(-1)**int(n)*(2*n+1)*tail(n,a,x)*tail(n,b,y)
        return mp.nsum(f,[0,mp.inf],method='alternating' if a*b==1 else 'richardson')
    points=[(mp.mpf('0.17'),mp.mpf('0.23')),
            (mp.mpc('0.11','0.07'),mp.mpc('-0.19','0.03')),
            (mp.mpc('-0.14','0.06'),mp.mpc('0.09','-0.12'))]
    records=[]
    for x,y in points:
        for a,b in [(1,1),(1,-1),(-1,1),(-1,-1)]:
            left=lhs(a,b,x,y);right=rhs(a,b,x,y)
            error=abs(left-right)
            assert error<mp.mpf('1e-45'),(a,b,x,y,error)
            records.append({'alpha':a,'beta':b,'x':str(x),'y':str(y),
                            'lhs':mp.nstr(left,50),'rhs':mp.nstr(right,50),
                            'absolute_error':mp.nstr(error,8)})
    for x,name,value in [(mp.mpf(0),'zero',mp.zeta(3)/2),
                          (mp.mpf(1)/2,'half',mp.pi*(2*mp.log(2)-1)),
                          (mp.mpf(1)/3,'third',3*mp.sqrt(3)*mp.pi*(mp.log(3)-1)/2),
                          (mp.mpf(1)/4,'quarter',2*mp.sqrt(2)*mp.pi*(3*mp.log(2)-2))]:
        left=lhs(-1,-1,x,x);error=abs(left-value)
        assert error<mp.mpf('1e-45'),(name,error)
        records.append({'specialization':name,'x':str(x),
                        'lhs':mp.nstr(left,50),'rhs':mp.nstr(value,50),
                        'absolute_error':mp.nstr(error,8)})
    return {'status':'passed','working_decimal_digits':mp.mp.dps,
            'checks':records,'meaning':'independent numerical consistency audit, not proof'}

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--numeric',action='store_true')
    parser.add_argument('--output',default='alternating_verification.json')
    args=parser.parse_args()
    result={'exact':exact_audit()}
    if args.numeric:
        result['numeric']=numeric_audit()
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'output':args.output,'exact_status':result['exact']['status'],
                      'coefficients_checked':result['exact']['coefficients_checked'],
                      'numeric_status':result.get('numeric',{}).get('status','not requested')}))
