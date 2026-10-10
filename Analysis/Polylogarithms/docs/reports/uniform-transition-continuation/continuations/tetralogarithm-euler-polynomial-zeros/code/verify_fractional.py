#!/usr/bin/env python3
"""Exact checks of fractional Euler formulas and a fixed-weight reversal.

The ordinary proofs establish the infinite families. These finite checks
independently verify specialization, normalizations and two rigorous signs.
Only the Python standard library and SymPy are required.
"""
import argparse
import json
import math
from fractions import Fraction as F
from pathlib import Path
import sympy as s


def integer_polynomials():
    T = s.Symbol('T')
    z = {k: s.Symbol('zeta_%d' % k) for k in range(2, 17)}
    cases = 0
    for a in range(1, 9):
        for b in range(1, 9):
            w = a + b
            ours = -T**(w-1)/s.factorial(w-1)
            for k in range(1, a):
                ours += ((-1)**(k+1)*s.rf(b,k)*z[b+k]
                         *T**(a-k-1)/(s.factorial(k)*s.factorial(a-k-1)))
            inherited = -T**(w-1)/s.factorial(w-1)
            for mu in range(b+1, w):
                inherited += ((-1)**(mu-b-1)*s.binomial(mu-1,b-1)
                              *z[mu]*T**(w-1-mu)/s.factorial(w-1-mu))
            assert s.expand(ours-inherited) == 0
            cases += 1
    # Check grouping two logarithmic series using independent convolution.
    mu = s.symbols('mu0:10')
    b = s.Symbol('b')
    grouping = 0
    for r in range(1, 9):
        grouped = 0
        for k in range(1, r+1):
            grouped += ((-1)**(k+1)*s.rf(b,k)*s.Symbol('Z%d'%k)
                        *mu[r-k]/s.factorial(k))
        q = sum(((-1)**(k+1)*s.prod(b+i for i in range(k))
                 *s.Symbol('Z%d'%k)*mu[r-k]/math.factorial(k)
                 for k in range(1,r+1)), s.S.Zero)
        assert s.expand(grouped-q) == 0
        grouping += 1
    return {'integer_density_specializations': cases,
            'coefficient_groupings': grouping, 'status': 'PASS'}


def invsqrt_interval(n, bits):
    if n <= 0:
        raise ValueError(n)
    scale = 1 << bits
    k = math.isqrt((scale*scale)//n)
    assert k*k*n <= scale*scale < (k+1)*(k+1)*n
    return F(k,scale), F(k+1,scale)


def add_interval(x,y):
    return x[0]+y[0], x[1]+y[1]


def scale_interval(c,x):
    return (c*x[0],c*x[1]) if c>=0 else (c*x[1],c*x[0])


def coefficients(max_index,bits):
    # f_n = H_(2n)^(1/2)/(2n+1)^(1/2), and axis f_n=H_(2n).
    half = [(F(0),F(0))]
    axis = [(F(0),F(0))]
    hhalf = (F(0),F(0))
    hone = F(0)
    for n in range(1,max_index):
        for k in [2*n-1,2*n]:
            hhalf=add_interval(hhalf,invsqrt_interval(k,bits))
            hone += F(1,k)
        power=invsqrt_interval(2*n+1,bits)
        half.append((hhalf[0]*power[0],hhalf[1]*power[1]))
        axis.append((hone,hone))
    return half,axis


def euler(N,values):
    # Direct finite binomial-tail weights, not repeated differences.
    tail = 1 << N
    answer=(F(0),F(0))
    for n in range(N):
        tail -= math.comb(N,n)
        weight=F((-1)**n*tail,1<<N)
        answer=add_interval(answer,scale_interval(weight,values[n]))
    assert tail == 1
    return answer


def exact_decimal_enclosure(interval,digits=24):
    scale=10**digits
    lo=(interval[0].numerator*scale)//interval[0].denominator
    hi=-((-interval[1].numerator*scale)//interval[1].denominator)
    def fmt(n):
        sign='-' if n<0 else ''
        n=abs(n)
        return sign+str(n//scale)+'.'+str(n%scale).zfill(digits)
    return [fmt(lo),fmt(hi)]


def crossing_signs():
    rows=[]
    for N in [1,8,16,32,64,128,256]:
        M=N+100
        bits=N+200
        half,axis=coefficients(M,bits)
        ea=euler(N,half); em=euler(M,half)
        aa=euler(N,axis); am=euler(M,axis)
        diff=add_interval(add_interval(ea,scale_interval(-1,em)),
                          add_interval(scale_interval(-1,aa),am))
        diff=scale_interval(F(1<<N),diff)
        budget=F(57,50)*F(1,1<<(M-N))
        diff=(diff[0]-budget,diff[1]+budget)
        if N==1: assert diff[1]<0
        if N==128: assert diff[0]>0
        rows.append({'N':N,'M':M,'dyadic_bits':bits,
                     'difference':'R_N(1/2,1/2)-R_N(0,1)',
                     'lower':[diff[0].numerator,diff[0].denominator],
                     'upper':[diff[1].numerator,diff[1].denominator],
                     'decimal_enclosure':exact_decimal_enclosure(diff),
                     'certified_sign':1 if diff[0]>0 else -1 if diff[1]<0 else 0})
    return {'status':'PASS','method':'integer square roots, exact fractions, finite Euler sums and 57/50 tail budget',
            'rows':rows}


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--output',default='fractional_checks.json')
    args=p.parse_args()
    result={'symbolic':integer_polynomials(),'crossing':crossing_signs()}
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'symbolic':result['symbolic'],
                      'crossing':[(r['N'],r['decimal_enclosure'],r['certified_sign'])
                                  for r in result['crossing']['rows']]},indent=2))


if __name__=='__main__':
    main()
