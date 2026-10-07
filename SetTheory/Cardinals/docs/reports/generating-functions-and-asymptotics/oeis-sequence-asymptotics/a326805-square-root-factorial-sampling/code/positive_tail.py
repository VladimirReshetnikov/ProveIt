#!/usr/bin/env python3
"""Exact rational upper bounds for the omitted positive square-root sample tail.

For integers n>=1 and T>n, c=1-n/T and f(u)=n**u/Gamma(1+u):
 psi(1+u)>log u gives f'(u)/f(u)<=-c for u>=T.
Since f(sqrt(t)) is decreasing there,
 sum_{k>T*T} f(sqrt(k)) <= int_{T*T}^infty f(sqrt(t))dt
 <= 2*n**T/T! * (T/c+1/c**2).
Only the displayed rational value and inequality to 10^-35 are checked by code;
the derivative and integral justification are in the manuscript. These bounds
alone do not certify floating evaluations or their integer floors.
"""
from fractions import Fraction as Q
from math import factorial
import json
import sys
sys.dont_write_bytecode = True
MAX_N, MAX_T = 1000, 10000


def need(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, low, high, name):
    need(type(value) is int and low <= value <= high,
         name+' must be an integer in ['+str(low)+', '+str(high)+']')


def tail_bound(n, T):
    integer(n, 1, MAX_N, 'n')
    integer(T, n+1, MAX_T, 'T')
    c = Q(T-n,T)
    return 2*Q(n**T,factorial(T))*(Q(T)/c+1/c**2)


def check_bound(n, T, claimed, threshold=Q(1,10**35)):
    need(type(claimed) is Q and type(threshold) is Q,
         'bound and threshold must be exact Fraction objects')
    need(threshold > 0, 'threshold must be positive')
    expected = tail_bound(n,T)
    need(claimed == expected, 'claimed rational bound differs from exact formula')
    need(0 < claimed < threshold, 'positive tail bound does not meet threshold')


def result():
    rows = []
    for n in range(1,35):
        T = 4*n+60
        bound = tail_bound(n,T)
        check_bound(n,T,bound)
        rows.append({'n':n,'T':T,'last_included_k':T*T,
                     'bound_numerator':str(bound.numerator),
                     'bound_denominator':str(bound.denominator),
                     'strictly_less_than_1_over_10_to_35':True})
    return {'status':'PASS','arithmetic':'exact fractions.Fraction',
            'rows':rows,'n0':'S(0)=1 exactly by continuity; tail is zero',
            'floating_floors_certified':False,
            'supported_n':[1,MAX_N],'supported_T':'integer n<T<=10000',
            'meaning':'upper bound on positive tail after k=T^2; no floating roundoff claim'}


if __name__ == '__main__':
    print(json.dumps(result(),sort_keys=True,indent=2,allow_nan=False))
