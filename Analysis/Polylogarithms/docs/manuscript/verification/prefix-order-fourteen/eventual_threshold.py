"""Construct an exact sufficient threshold for a fixed even tail order.

This implements the coefficient-defined constants of the eventual-rank
proof. It never infers the infinite theorem from the examples computed.
Requires SymPy. Default examples a=1,2,3,4 are verification diagnostics;
the article supplies the arbitrary-a proof and termination argument.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import sympy as sp
from sympy.functions.combinatorial.numbers import stirling


def falling(x, n):
    return sp.prod(x-r for r in range(n))


def threshold(a):
    if a < 1:
        raise ValueError('a must be a positive integer')
    b, y = sp.symbols('b y')
    U = sp.symbols(f'U1:{2*a}')
    n = [b-a+i for i in range(a)]
    R = [2*b-2*a+2+2*ell for ell in range(a)]
    J = sp.prod((2*ni+1)*(2*ni+2) for ni in n)
    E = sp.prod(R[ell]+r for i in range(a) for ell in range(a)
                for r in range(1,max(0,2*i-4*ell-1)+1))
    e = sum(max(0,2*i-4*ell-1) for i in range(a) for ell in range(a))
    D = math.factorial(2*a)*J*E
    g = 6*a*a-4*a+a*e
    max_norm = 0
    max_degree = 0
    checks = 0
    for i in range(a):
        ni = n[i]
        ordinary = sp.Poly(sp.expand((2*ni+2-y)*falling(4*ni+2-y,2*i)),y)
        d = {h:sp.expand(sum(ordinary.nth(k)*stirling(k,h,kind=2)
                      for k in range(h,2*i+2))) for h in range(2*i+2)}
        assert sp.expand(d[1]+(i+1)*falling(4*ni+2,2*i))==0
        for ell in range(a):
            N = 2*(ni-ell)+1
            diff = 1+4*ell-2*i
            factorial_ratio = (sp.prod(N+r for r in range(1,diff+1)) if diff>=0
                               else 1/sp.prod(R[ell]+r for r in range(1,-diff+1)))
            F = sp.prod((2*ni-r)*(2*ni+3+r) for r in range(2*ell))/sp.factorial(2*ell+1)
            correction = sum(d[2*k+1]*falling(N,2*k+1)*U[a-i+ell+k-1]
                             for k in range(i+1))
            entry = 2*F+factorial_ratio*correction/((2*ni+1)*(2*ni+2)*math.factorial(2*ell+2))
            scaled = sp.Poly(sp.cancel(D*entry),b,*U,domain=sp.ZZ)
            max_norm = max(max_norm,sum(abs(int(c)) for _,c in scaled.terms()))
            max_degree = max(max_degree,max(powers[0] for powers,_ in scaled.terms()))
            # Verify the finite factorial cancellation behind the general proof.
            for k in range(i+1):
                j = a-i+ell+k
                alpha = sp.prod(2*b-4*a+2+r for r in range(1,4*a-2-2*j+1))
                sigma = sp.prod(2*b-4*a+2+r for r in range(1,2*a+2*ell+1))/sp.factorial(2*ell+2)
                left = factorial_ratio*falling(N,2*k+1)*alpha/math.factorial(2*ell+2)
                assert sp.cancel(left-sigma)==0
                checks += 1
    assert max_degree <= 6*a+e-4
    norm_K = math.factorial(a)*max_norm**a
    kappa = Fraction(math.factorial(a)*math.factorial(2*a)**a,
                     math.prod(math.factorial(2*ell+2) for ell in range(a)))
    points = [Fraction(1,j*j) for j in range(1,a+1)]
    V = math.prod((points[j]-points[i])**2 for i in range(a) for j in range(i+1,a))
    L = 4*(a-1)**2
    chi = 2*a*a-6*a+2
    C = Fraction(norm_K*8**(a-1+max(chi,0))*2**L,
                 kappa*4**a*V*math.factorial(a)**(4*a-2))
    B0 = max(4*a+10,L,16*math.factorial(a))
    B = B0
    bound = C*B**L*(8*math.factorial(a))**(2*B)/math.factorial(2*B-4*a+2)
    while bound>=1:
        bound *= Fraction(B+1,B)**L*Fraction((8*math.factorial(a))**2,
                                            (2*B-4*a+4)*(2*B-4*a+3))
        B+=1
    assert bound<1
    # Confirm the ratio claim at the start with exact rationals.
    ratio = Fraction(B0+1,B0)**L*Fraction((8*math.factorial(a))**2,
                                       (2*B0-4*a+4)*(2*B0-4*a+3))
    assert ratio<Fraction(3,4)
    print(f'a={a}: B0={B0}, B={B}, coefficient norm E*={max_norm}',flush=True)
    return {'a':a,'p':2*a,'D_degree':2*a+e,'e':e,'g':g,
            'max_scaled_entry_b_degree':max_degree,'scaled_entry_norm_E':max_norm,
            'determinant_norm_bound_K':norm_K,'kappa':str(kappa),'V':str(V),
            'L':L,'chi':chi,'C':str(C),'B0':B0,'sufficient_B':B,
            'factorial_cancellation_checks':checks,
            'all_exact_checks_passed':True}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('orders',nargs='*',type=int,default=[1,2,3,4],
                        help='positive a values (the smaller tail order is p=2a)')
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('eventual_threshold_checks.json'))
    args=parser.parse_args()
    result={'theorem':'For every fixed a, the displayed constructive bound B proves rank for all b>=B.',
            'examples_are_not_the_proof':True,'cases':[threshold(a) for a in args.orders]}
    args.output.write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':
    main()
