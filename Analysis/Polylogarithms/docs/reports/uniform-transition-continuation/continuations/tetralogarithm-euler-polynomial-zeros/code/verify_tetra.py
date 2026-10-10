#!/usr/bin/env python3
"""Exact replay and endpoint evaluation of the rational Li_4 certificate."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from pathlib import Path
import json
from functools import reduce
from math import gcd
import sympy as sp
import mpmath as mp
t=sp.Symbol('t')

def fv(expression):
    """Exact Q(t)* tensor Q factorization, including rational prime contents."""
    result=defaultdict(int)
    numerator,denominator=sp.fraction(sp.cancel(expression))
    for polynomial,polarity in ((numerator,1),(denominator,-1)):
        content,factors=sp.factor_list(polynomial,t)
        for prime,multiplicity in sp.factorint(abs(sp.numer(content))).items():
            result[('prime',int(prime))]+=polarity*int(multiplicity)
        for prime,multiplicity in sp.factorint(sp.denom(content)).items():
            result[('prime',int(prime))]-=polarity*int(multiplicity)
        rebuilt=content
        for factor,multiplicity in factors:
            p=sp.Poly(factor,t,domain=sp.ZZ)
            assert p.LC()>0
            assert sp.gcd_list(p.all_coeffs())==1
            result[('poly',tuple(map(int,p.all_coeffs())))]+=polarity*int(multiplicity)
            rebuilt*=factor**multiplicity
        assert sp.expand(rebuilt-polynomial)==0
    return {key:value for key,value in result.items() if value}

ROOT=Path(__file__).resolve().parent
A,B,Z2,Z3,Z4=sp.symbols('A B Z2 Z3 Z4')
L2,L3,L4=sp.symbols('L2 L3 L4')
BASE=(('prime',2),('poly',(1,0)),('poly',(1,-1)),('poly',(1,1)))

def logq(q):
    q=Q(q)
    assert q>0
    d=defaultdict(int)
    for p,e in sp.factorint(q.numerator).items():d[int(p)]+=int(e)
    for p,e in sp.factorint(q.denominator).items():d[int(p)]-=int(e)
    return sum(e*({2:A,3:B}.get(p,sp.Symbol('log'+str(p)))) for p,e in d.items())

def poly4(q):
    """Re Li4(q) -> positive arguments <=1, plus exact inversion polynomial."""
    q=Q(q)
    if q==0:return {},sp.Integer(0)
    if q==1:return {},Z4
    if q==-1:return {},-sp.Rational(7,8)*Z4
    sign=1 if q>0 else -1
    r=abs(q);co=sp.Integer(1);P=sp.Integer(0)
    if r>1:
        l=logq(r)
        P=(-l**4/24+Z2*l*l+2*Z4) if sign>0 else (-l**4/24-Z2*l*l/2-sp.Rational(7,4)*Z4)
        r=1/r;co=sp.Integer(-1)
    if sign>0:return {r:co},P
    return {r:-co,r*r:co/8},P

def low(n,x):
    x=Q(x)
    assert x in [Q(1),Q(-1),Q(1,2),Q(2)]
    if x==1:
        assert n!=1, 'Li1(1) must never be evaluated'
        return {2:Z2,3:Z3}[n]
    if x==-1:return {2:-Z2/2,3:-sp.Rational(3,4)*Z3,1:-A}[n]
    if x==Q(1,2):return {2:Z2/2-A*A/2,3:sp.Rational(7,8)*Z3-Z2*A/2+A**3/6,1:A}[n]
    return {2:sp.Rational(3,2)*Z2,3:sp.Rational(7,8)*Z3+sp.Rational(3,2)*Z2*A,1:sp.Integer(0)}[n]

def weighted_low1(coefficient,endpoint):
    """The endpoint-one product is zero without assigning a value to Li1(1)."""
    if endpoint==1:
        assert sp.expand(coefficient)==0
        return sp.Integer(0)
    return coefficient*low(1,endpoint)

def general_polynomial(rows,scale):
    X,Y,Z=sp.symbols('X Y Z')
    base={('prime',2):A,('poly',(1,0)):X,('poly',(1,-1)):Y,('poly',(1,1)):Z}
    half=sp.Symbol('Li4half')
    polynomial=sp.Integer(0)
    for original,sign,(d,a,b,c),f,r,endpoint in rows:
        co=original/scale
        L=d*A+a*X+b*Y+c*Z
        M=sp.Integer(0)
        for key,value in fv(1-f).items():
            M+=value*base.get(key,sp.Symbol('extra_'+str(key)))
        polynomial-=co*L**3*M/24
        if endpoint:
            M0=d*A;D=L-M0
            polynomial+=co*(D*low(3,endpoint)+D**2*low(2,endpoint)/2+
                          weighted_low1(-M0**3/8+L*M0**2/3-L**2*M0/4,endpoint))
            if endpoint==1:C=Z4
            elif endpoint==-1:C=-sp.Rational(7,8)*Z4
            elif endpoint==Q(1,2):C=half
            elif endpoint==2:C=-half-A**4/24+Z2*A*A+2*Z4
            else:raise AssertionError('Unexpected endpoint')
            polynomial+=co*C
    polynomial=sp.expand(polynomial-4*half)
    P4=(A**4/4-A**3*(Y+Z)/6+A**2*(Y**2+Z**2)/4+
        5*A*(Y**3+Z**3)/6-X*Y*(3*Y+Z)*(Y+Z)+
        (17*Y**4+8*Y**3*Z+9*Y**2*Z**2+2*Y*Z**3+2*Z**4)/6)
    P2=-6*A*A-4*A*(Y+Z)+sp.Rational(5,2)*Y*Y+8*Y*Z-8*Z*Z
    expected=P4+Z2*P2-sp.Rational(71,4)*Z4
    assert sp.expand(polynomial-expected)==0
    assert polynomial.free_symbols <= {A,X,Y,Z,Z2,Z4}
    return polynomial,(X,Y,Z),P4,P2

def numerical_audit(rows,scale,polynomial,variables):
    mp.mp.dps=90
    X,Y,Z=variables
    evaluate=sp.lambdify((A,X,Y,Z,Z2,Z4),polynomial,modules='mpmath')
    records=[]
    for value in (Q(1,5),Q(37,100),Q(1,2),Q(4,5)):
        x=mp.mpf(value.numerator)/value.denominator
        lhs=mp.fsum(mp.mpf(str(co/scale))*mp.re(mp.polylog(4,
              sign*mp.mpf(2)**d*x**a*(1-x)**b*(1+x)**c))
              for co,sign,(d,a,b,c),f,r,e in rows)-4*mp.polylog(4,mp.mpf('0.5'))
        rhs=evaluate(mp.log(2),mp.log(x),mp.log(1-x),mp.log(1+x),mp.zeta(2),mp.zeta(4))
        error=abs(lhs-rhs)
        assert error<mp.mpf('1e-75')
        records.append({'t':str(value),'absolute_residual':mp.nstr(error,12)})
    return {'working_decimal_digits':90,'role':'independent numerical audit only',
            'functional_identity_checks':records}

def verify_additional_specializations(cases,rows,scale,polynomial,variables):
    """Replay rational specializations without altering the tensor proof."""
    X,Y,Z=variables
    records=[]
    for case in cases:
        parameter=Q(case['parameter'])
        normalization=sp.Rational(case['normalization_from_primitive_functional_identity'])
        image=defaultdict(lambda:sp.Integer(0))
        image[Q(1,2)]=-4
        inversion=sp.Integer(0)
        for original,sign,(d,a,b,c),f,r,endpoint in rows:
            co=original/scale
            argument=Q(sign)*Q(2)**d*parameter**a*(1-parameter)**b*(1+parameter)**c
            terms,p=poly4(argument)
            for key,value in terms.items():image[key]+=co*value
            inversion+=co*p
        image={key:normalization*value for key,value in image.items() if value}
        assert all(value.q==1 for value in image.values())
        assert reduce(gcd,[abs(int(value)) for value in image.values()],0)==1
        actual={str(key):str(value) for key,value in sorted(image.items())}
        assert actual==case['target'],(actual,case['target'])
        result=sp.expand(normalization*(polynomial.subs({
            X:logq(parameter),Y:logq(1-parameter),Z:logq(1+parameter)})-inversion))
        expected=sp.sympify(case['rhs'],locals={'A':A,'B':B,'Z2':Z2,'Z4':Z4})
        assert sp.expand(result-expected)==0
        mp.mp.dps=90
        lhs=mp.fsum(mp.mpf(str(co))*mp.polylog(4,mp.mpf(key.numerator)/key.denominator)
                     for key,co in image.items())
        evaluate=sp.lambdify((A,B,Z2,Z4),expected,modules='mpmath')
        rhs=evaluate(mp.log(2),mp.log(3),mp.zeta(2),mp.zeta(4))
        error=abs(lhs-rhs)
        assert error<mp.mpf('1e-75')
        records.append({'parameter':str(parameter),'status':'PASS','terms':len(image),
            'primitive_integer_coefficients':True,'positive_Li4_image':actual,
            'rhs':str(result),'exact_polynomial_difference':0,
            'numerical_audit_working_digits':90,'numerical_audit_absolute_residual':mp.nstr(error,12)})
    return records

def main():
    case=json.loads((ROOT/'tetralogarithm_certificate.json').read_text())
    rows=[];residual=defaultdict(lambda:sp.Integer(0));coords=set()
    allkeys=set(BASE)
    for coefficient,sign,d,a,b,c in case['rows']:
        co=sp.Rational(coefficient)*case['normalization_scale']
        f=sign*sp.Rational(2)**d*t**a*(1-t)**b*(1+t)**c
        e=(d,a,b,c)
        u={k:v for k,v in zip(BASE,e) if v}
        assert fv(f)==u
        v=fv(1-f);allkeys.update(v)
        for pre in combinations_with_replacement(range(4),2):
            cp=co*e[pre[0]]*e[pre[1]]
            for ku,eu in u.items():
                for kv,ev in v.items():
                    if ku==kv:continue
                    k,l=sorted((ku,kv),key=str)
                    residual[pre+(k,l)]+=cp*eu*ev*(1 if k==ku else -1)
        r=Q(sign)*Q(3)**c*Q(2)**(d-a-b-c)
        endpoint=Q(sign)*Q(2)**d if a==0 else Q(0)
        rows.append((co,sign,e,f,r,endpoint))
    assert not any(residual.values()),'Beta4 certificate failed'
    # Contraction and inversion of R4 = Li4 - L Li3 + L² Li2/2 - L³ Li1/8.
    rhs=sp.Integer(0);poly=sp.Integer(0);actual=defaultdict(lambda:sp.Integer(0))
    for co,sign,(d,a,b,c),f,r,endpoint in rows:
        L=(d-a-b-c)*A+c*B
        if r!=1:rhs+=co*L**3*(-logq(abs(1-r)))/24
        else:assert L==0
        if endpoint:
            M=d*A;D=L-M
            rhs+=co*(D*low(3,endpoint)+D**2*low(2,endpoint)/2+
                     weighted_low1(-M**3/8+L*M*M/3-L*L*M/4,endpoint))
        for q,sgn in [(r,1),(endpoint,-1)]:
            image,p=poly4(q)
            for key,val in image.items():actual[key]+=sgn*co*val
            poly+=sgn*co*p
    actual={str(k):str(v) for k,v in actual.items() if v}
    assert actual==case['target'],(actual,case['target'])
    result=sp.expand(rhs-poly)
    expected=(19*90*Z4+30*(6*Z2-B**2)*(10*A*A-12*A*B+3*B*B)-30*A*A*(19*A*A-24*A*B+8*B*B))
    print('RHS',result)
    print('Expected difference',sp.expand(result-expected))
    assert sp.expand(result-expected)==0
    polynomial,variables,P4,P2=general_polynomial(rows,case['normalization_scale'])
    audit=numerical_audit(rows,case['normalization_scale'],polynomial,variables)
    specializations=verify_additional_specializations(case.get('additional_specializations',[]),
                    rows,case['normalization_scale'],polynomial,variables)
    receipt={'status':'PASS','proof':'exact beta4 tensor certificate plus elementary endpoint descent',
      'rows':len(rows),'nonzero_tensor_residual':False,'tensor_coordinates':len(residual),
      'factor_coordinates':len(allkeys),'rational_prime_factors':[k[1] for k in allkeys if k[0]=='prime'],
      'specialization_image':actual,'endpoint_rhs':str(sp.expand(rhs)),
      'Li4_inversion_polynomial':str(sp.expand(poly)),'final_rhs':str(result),
      'matches_conjecture_exactly':True,
      'general_functional_identity_exact':True,
      'general_polynomial_P4':str(P4),'general_polynomial_P2':str(P2),
      'general_functional_rhs':str(polynomial),'numerical_audit':audit,
      'additional_specializations':specializations}
    (ROOT/'tetralogarithm_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
