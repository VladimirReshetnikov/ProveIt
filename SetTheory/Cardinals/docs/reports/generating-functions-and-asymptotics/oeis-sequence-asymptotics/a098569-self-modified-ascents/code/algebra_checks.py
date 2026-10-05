#!/usr/bin/env python3
"""Exact finite Gaussian, moment, ratio, and inverse-seed algebra."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
if not hasattr(sys, 'set_int_max_str_digits'):
    raise RuntimeError('Python 3.11 or newer is required')
sys.set_int_max_str_digits(640)
import argparse
from math import factorial, prod
import sympy as s
from common import REPORT_NUMBER, emit, integer, new_file_path, require

LAM = s.symbols('lambda3:9')
ETA = s.symbols('eta1:7')


def gaussian_moment(degree):
    integer(degree,0,32,'Gaussian moment degree')
    return 0 if degree%2 else prod(range(1,degree,2))


def contraction_terms(order,binary=False):
    """Return coefficient and exponent tuples of total weight 2*order."""
    integer(order,0,3,'contraction order')
    require(isinstance(binary,bool),'binary flag must be bool')
    if binary:integer(order,0,2,'binary contraction order')
    variables=[(j,j-2) for j in range(3,9)]+([(j,j) for j in range(1,7)] if binary else [])
    result=[]
    def visit(index,remaining,degree,denominator,powers):
        if index==len(variables):
            if remaining==0:
                result.append((s.Rational(gaussian_moment(degree),denominator),tuple(powers)))
            return
        j,weight=variables[index]
        for k in range(remaining//weight+1):
            visit(index+1,remaining-k*weight,degree+j*k,
                  denominator*factorial(k)*factorial(j)**k,powers+[k])
    visit(0,2*order,0,1,[])
    return result


def contraction(order,binary=False):
    variables=LAM+(ETA if binary else ())
    return s.expand(sum(coefficient*prod(v**k for v,k in zip(variables,powers))
                        for coefficient,powers in contraction_terms(order,binary)))


def _gaussian_polynomial(poly,z):
    result=0
    for (degree,),coefficient in s.Poly(s.expand(poly),z).terms():
        result+=coefficient*gaussian_moment(degree)
    return s.expand(result)


def verify():
    l3,l4,l5,l6,_,_=LAM
    e1,e2,e3,e4,_,_=ETA
    C1=l4/8+5*l3**2/24
    C2=l6/48+7*l3*l5/48+35*l4**2/384+35*l3**2*l4/64+385*l3**4/1152
    require(s.expand(contraction(1)-C1)==0,'C1 Gaussian contraction')
    require(s.expand(contraction(2)-C2)==0,'C2 Gaussian contraction')
    Q1=(e1**2+e2+e1*l3)/2
    Q2=(e1**4/8+5*e1**3*l3/12+3*e1**2*e2/4+5*e1**2*l3**2/8+e1**2*l4/4
        +5*e1*e2*l3/4+e1*e3/2+5*e1*l3**3/8+2*e1*l3*l4/3+e1*l5/8
        +3*e2**2/8+5*e2*l3**2/8+e2*l4/4+5*e3*l3/12+e4/8)
    G1=contraction(1,True);G2=contraction(2,True)
    require(s.expand(G1-C1-Q1)==0,'binary Q1 quotient')
    require(s.expand(G2-C1*Q1-C2-Q2)==0,'binary Q2 quotient')
    # Independent exponent-series route through weight four.
    z=s.symbols('z')
    P1=e1*z+l3*z**3/6;P2=e2*z**2/2+l4*z**4/24
    P3=e3*z**3/6+l5*z**5/120;P4=e4*z**4/24+l6*z**6/720
    require(s.expand(_gaussian_polynomial(P2+P1**2/2,z)-G1)==0,'independent G1 exponent series')
    require(s.expand(_gaussian_polynomial(P4+P1*P3+P2**2/2+P1**2*P2/2+P1**4/24,z)-G2)==0,
            'independent G2 exponent series')
    mean=_gaussian_polynomial(z*l3*z**3/6,z)
    raw2=_gaussian_polynomial(z**2*(l4*z**4/24+l3**2*z**6/72),z)-C1
    variance=s.expand(raw2-mean**2)
    require(mean==l3/2,'standardized first moment')
    require(s.expand(raw2-l4/2-5*l3**2/4)==0,'standardized raw second moment')
    require(s.expand(variance-l4/2-l3**2)==0,'standardized variance')
    leading={LAM[j-3]:2**s.Rational(2-j,2)*(-1)**(j-1)*factorial(j-1) for j in range(3,9)}
    require(s.simplify(C1.subs(leading)-s.Rational(1,24))==0,'leading N*C1')
    require(s.simplify(C2.subs(leading)-s.Rational(1,1152))==0,'leading N^2*C2')
    u=s.symbols('u',positive=True)
    D=u+4+2/u;E=2*u+6-4/u**2;F=(u+1)*(u+2);G=(u+2)*(3*u+4);B=-F/2+1/u
    R=u*(u+2)*(u**4+8*u**3+22*u**2+20*u+8)/(4*(u**2+4*u+2)**2)
    correction=u+F*B/D+(F**2-G)/(2*D)+E*F/(2*D**2)
    require(s.cancel((u+2)*correction/2-R)==0,'explicit-u probability correction')
    Nu=u*(u+2)*s.exp(u)/2
    F0=Nu*u*(u+1)/(u+2)
    require(s.simplify(s.diff(F0,u)/s.diff(Nu,u)-u)==0,'smooth inverse slope F0 prime equals u')
    require(s.simplify(F0-u**2*(u+1)*s.exp(u)/2)==0,'inverse v seed equation')
    P=u**2+4*u+2
    gp=u**2/4+u/2-s.log(P/2)/2;gm=-u**2/4-u/2-s.log(P/2)/2
    require(s.simplify((-gm+gp)/u-u/2-1)==0,'ordinary/binary elementary inverse separation')
    return {'status':'PASS','report_number':REPORT_NUMBER,
            'scope':'Exact rational/symbolic finite identities; analytic remainders are proved in the article',
            'C1':str(C1),'C2':str(C2),'C3':str(contraction(3)), 'Q1':str(Q1),'Q2':str(Q2),
            'contraction_term_counts':{'C1':len(contraction_terms(1)),'C2':len(contraction_terms(2)),
                                       'C3':len(contraction_terms(3)),'G1':len(contraction_terms(1,True)),
                                       'G2':len(contraction_terms(2,True))},
            'checked_identities':['C1 and C2 explicit contractions','Q1 and Q2 quotient contractions',
                                  'G1 and G2 independent exponent series','standardized mean and raw second moment',
                                  'standardized variance','leading C1 and C2 constants','explicit-u R(u) simplification',
                                  'F0 derivative identity','inverse v seed equation','elementary inverse separation'],
            'sympy_version':s.__version__}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output')
    args=parser.parse_args()
    if args.output is not None:new_file_path(args.output)
    emit(verify(),args.output)


if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
