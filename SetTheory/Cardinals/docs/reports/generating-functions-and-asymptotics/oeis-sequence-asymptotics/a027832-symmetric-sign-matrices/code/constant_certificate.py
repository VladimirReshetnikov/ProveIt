#!/usr/bin/env python3
"""Exact rational enclosures of ell and the displayed leading constants.

Machin's identity, alternating Taylor series and integer square roots only.
This certificate does not bound the asymptotic enumeration remainder.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from fractions import Fraction as F
import math
from common import emit, integer, new_file_path, require

TERMS = 64
SQRT_DIGITS = 90


def _add(A,B): return (A[0]+B[0], A[1]+B[1])
def _neg(A): return (-A[1],-A[0])
def _sub(A,B): return _add(A,_neg(B))
def _mul(A,B):
    products=[a*b for a in A for b in B]
    return (min(products),max(products))
def _recip(A):
    require(A[0] > 0, 'certificate reciprocal requires positive interval')
    return (1/A[1],1/A[0])
def _div(A,B):return _mul(A,_recip(B))
def _point(x):return (F(x),F(x))
def _square(A):
    require(A[0] >= 0, 'certificate square requires nonnegative interval')
    return (A[0]*A[0],A[1]*A[1])


def _sqrt_point(x):
    require(x >= 0, 'negative square root')
    scale=10**SQRT_DIGITS
    lower=math.isqrt(x.numerator*scale*scale//x.denominator)
    return (F(lower,scale),F(lower+1,scale))


def _sqrt(A):return (_sqrt_point(A[0])[0],_sqrt_point(A[1])[1])


def _arctan_reciprocal(q):
    x=F(1,q)
    total=F(0)
    for j in range(96):
        total += (-1)**j*x**(2*j+1)/(2*j+1)
    following=x**193/193
    return (total,total+following)


def _pi_interval():
    return _sub(_mul(_point(16),_arctan_reciprocal(5)),
                _mul(_point(4),_arctan_reciprocal(239)))


def _exp_point(x):
    require(abs(x) <= 2, 'exponential certificate domain exceeded')
    if x > 0:
        return _recip(_exp_point(-x))
    # Sixty-four terms, ending at the negative odd term, give a lower bound.
    total=F(1);term=F(1)
    for j in range(1,TERMS):
        term *= x/j
        total += term
    following=term*x/TERMS
    require(following >= 0 and total > 0, 'Taylor enclosure orientation')
    return (total,total+following)


def _exp(A):return (_exp_point(A[0])[0],_exp_point(A[1])[1])


def _integral_point(x):
    require(0 <= x <= 1, 'normal-integral certificate domain exceeded')
    total=F(0)
    for j in range(TERMS):
        total += (-1)**j*x**(2*j+1)/(2**j*math.factorial(j)*(2*j+1))
    following=x**(2*TERMS+1)/(2**TERMS*math.factorial(TERMS)*(2*TERMS+1))
    return (total,total+following)


def _root_function(x,root_pi_half):
    # Multiplying phi(x)-x Phi(x) by sqrt(2 pi) avoids dividing intervals.
    return _sub(_exp_point(-x*x/2),_mul(_point(x),_add(root_pi_half,_integral_point(x))))


def _decimal_interval(A,digits):
    scale=10**digits
    lo=A[0].numerator*scale//A[0].denominator
    hi=-((-A[1].numerator*scale)//A[1].denominator)
    def render(value):
        sign='-' if value < 0 else ''
        value=abs(value)
        return sign+str(value//scale)+'.'+str(value%scale).zfill(digits)
    return {'lower':render(lo),'upper':render(hi)}


def certified_constants(digits=30):
    integer(digits,20,40,'certificate decimal digits')
    pi=_pi_interval();root_pi_half=_sqrt(_div(pi,_point(2)))
    lo,hi=F(1,2),F(51,100)
    require(_root_function(lo,root_pi_half)[0] > 0, 'left root endpoint not certified')
    require(_root_function(hi,root_pi_half)[1] < 0, 'right root endpoint not certified')
    steps=4*(digits+10)
    for _ in range(steps):
        mid=(lo+hi)/2
        value=_root_function(mid,root_pi_half)
        if value[0] > 0:
            lo=mid
        elif value[1] < 0:
            hi=mid
        else:
            raise RuntimeError('Taylor bounds cannot decide root sign at this precision')
    require(_root_function(lo,root_pi_half)[0] > 0 and
            _root_function(hi,root_pi_half)[1] < 0,'final root signs not certified')
    ell=(lo,hi);ell2=_square(ell);ell4=_square(ell2)
    Phi=_add(_point(F(1,2)),_div((_integral_point(lo)[0],_integral_point(hi)[1]),
                                     _sqrt(_mul(_point(2),pi))))
    denominator=_add(_point(1),_mul(_point(2),ell2))
    q=_mul(Phi,_exp(_neg(_div(ell2,_point(2)))))
    Z0=_div(_exp(_sub(_mul(_point(F(5,4)),ell2),_div(ell4,_point(2)))),_sqrt(denominator))
    J=_neg(_div(_mul(_point(4),ell2),denominator))
    base=_mul(Z0,_exp(_neg(_div(ell2,_point(2)))))
    intervals={'pi':pi,'ell':ell,'Phi_ell':Phi,'one_over_Phi_ell':_recip(Phi),
               'q':q,'Z0':Z0,'J':J,'odd_prefactor':base,
               'even_prefactor':_mul(base,_exp(_div(J,_point(4)))),
               'critical_quadratic_coefficient':_div(ell2,_mul(_point(2),denominator)),
               'critical_linear_coefficient':_div(_mul(_point(2),ell),denominator),
               'v':_div(_sub(_point(1),_mul(_point(2),ell2)),_point(4))}
    require(intervals['v'][0] > 0 and intervals['v'][1] < F(1,4), 'limiting variance interval')
    return {'status':'CERTIFIED_RATIONAL_ENCLOSURES','arithmetic':'fractions.Fraction and integer isqrt',
            'decimal_digits':digits,'root_bisections':steps,
            'machin_arctan_terms':96,'alternating_series_terms':TERMS,
            'square_root_decimal_grid':SQRT_DIGITS,
            'root_endpoint_signs':'strictly positive at lower; strictly negative at upper',
            'root_uniqueness':'F(x)=exp(-x^2/2)-x(sqrt(pi/2)+integral_0^x exp(-t^2/2)dt) has negative derivative for x>=0',
            'intervals':{name:_decimal_interval(A,digits) for name,A in intervals.items()},
            'scope':'Encloses these constants only. Does not certify a finite-n asymptotic error, onset, inverse threshold, or all-order expansion.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--digits',type=int,default=30)
    parser.add_argument('--output')
    args=parser.parse_args()
    integer(args.digits,20,40,'certificate decimal digits')
    if args.output is not None:new_file_path(args.output)
    emit(certified_constants(args.digits),args.output)


if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
