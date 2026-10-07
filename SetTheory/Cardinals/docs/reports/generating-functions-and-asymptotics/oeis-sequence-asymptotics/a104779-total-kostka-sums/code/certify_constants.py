#!/usr/bin/env python3
"""Forty-decimal rational certificates for the low support constants.

The enclosure uses exact finite fractions and the article's proved factorial
bounds. Floating-point arithmetic is never used in this program.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from fractions import Fraction as F
from math import factorial
from common import emit, require, new_file_path
from exact_counts import partitions, centralizer, square_roots, _multiply, _reciprocal

J=70
DIGITS=40
EXPECTED={
 'C':('2.5294774720791526481801161542539542411787','2.5294774720791526481801161542539542411788'),
 '3':('0.9887340176119067106765900015027659522294','0.9887340176119067106765900015027659522295'),
 '4':('6.0121093539050841781399993190129528805222','6.0121093539050841781399993190129528805223'),
 '5':('0.5456358974558364595261891034594968055729','0.5456358974558364595261891034594968055730'),
 '6':('3.1846595830270382795159539520700360539731','3.1846595830270382795159539520700360539732')}

def _decimal(i):
    q,r=divmod(i,10**DIGITS)
    return str(q)+'.'+str(r).rjust(DIGITS,'0')

def _enclosure(value,error,label):
    scale=10**DIGITS
    lo=value.numerator*scale//value.denominator
    upper=value+error
    hi=(upper.numerator*scale+upper.denominator-1)//upper.denominator
    require(hi-lo==1,'one-unit decimal enclosure not achieved')
    pair=(_decimal(lo),_decimal(hi))
    require(pair==EXPECTED[label],'certified decimal fixture mismatch')
    return {'lower':pair[0],'upper':pair[1], 'digits':DIGITS,
            'width_units_of_10_minus_digits':hi-lo}

def verify():
    C=F(1)
    for j in range(2,J+1):
        C*=F(factorial(j),factorial(j)-1)
    def D(k):
        return sum((F(factorial(j),factorial(j-k)*(factorial(j)-1))
                    for j in range(max(k,2),J+1)),F())
    def a(j):
        return F(j*(j-1),2*(factorial(j)-1))
    def b(j):
        return F(j*(j-1)*(j-2),3*(factorial(j)-1))
    H={3:D(3)/3,
       4:D(4)/4+(D(2)/2)**2+sum((a(j)**2 for j in range(2,J+1)),F()),
       5:D(5)/5,
       6:2*D(6)/9+2*(D(3)/3)**2+2*sum((b(j)**2 for j in range(3,J+1)),F())}
    # Independently construct the full multivariate truncated product at the
    # same J: this verifies all repeated-same-factor terms in the low formulas.
    parts=[p for s in range(2,7) for p in partitions(s,2)]
    product={():F(1)}
    for j in range(2,J+1):
        d={p:F(factorial(j),factorial(j-sum(p))*(factorial(j)-1)*centralizer(p))
           for p in parts if sum(p)<=j}
        product=_multiply(product,_reciprocal(d,6),6)
    by_support={s:sum((v*square_roots(p) for p,v in product.items() if sum(p)==s),F())
                for s in range(7)}
    require(by_support[0]==1 and by_support[1]==by_support[2]==0,'low support vanishing')
    require(all(by_support[s]==v for s,v in H.items()),'low support formula disagreement')
    # Companion constants check q_(2), q_(3), q_(4), q_(2,2) independently.
    eta=D(2)/2
    require(product[(2,)]==eta and product[(3,)]==H[3],'single-cycle coefficients')
    require(product[(4,)]==D(4)/4 and product[(2,2)]==H[4]/2,'support-four coefficients')
    for sign in (1,-1):
        result={s:sum((centralizer(p)*v*v*(sign**(s-len(p)))
                       for p,v in product.items() if sum(p)==s),F()) for s in range(2,5)}
        require(result=={2:sign*2*eta**2,3:3*H[3]**2,4:sign*D(4)**2/4+2*H[4]**2},
                'companion low-support coefficient formula')
    out={'status':'PASS','J':J,'digits':DIGITS,'C':_enclosure(C,F(6*(J+2),(J+1)*factorial(J+1)),'C'),'H':{}}
    for s,v in H.items():
        R=max(square_roots(p) for p in partitions(s,2))
        error=F(24*s*R*4**s*(J+1)**s,factorial(J+1))
        out['H'][str(s)]=_enclosure(v,error,str(s))
    out.update(arithmetic='exact fractions.Fraction; outward decimal rounding by integer division',
               low_support_formulas_verified_at_J=J,
               companion_formulas_verified_at_J=J,
               C_tail='6*(J+2)/((J+1)*(J+1)!)',
               H_s_tail='24*s*R_s*4^s*(J+1)^s/(J+1)!',
               scope='Certified constant enclosures conditional only on the analytic tail inequalities proved in the article; no finite-n remainder or inverse-rounding certificate.')
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    args=parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(verify(),args.output)

if __name__=='__main__':
    try:
        main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:
        raise SystemExit(str(exc))
