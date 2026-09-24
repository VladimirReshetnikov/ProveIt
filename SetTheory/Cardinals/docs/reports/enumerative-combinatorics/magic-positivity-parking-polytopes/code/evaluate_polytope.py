#!/usr/bin/env python3
"""Evaluate the certified Ehrhart, magic, and h*-polynomials in dimensions 2..10."""
from __future__ import annotations
import argparse
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json
from sparse_magic import evaluate, read_poly


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('parameters',type=int,nargs='+',help='Positive integers b1 ... bn')
    parser.add_argument('--dilation',type=int,default=1)
    parser.add_argument('--certificates',type=Path,
                        default=Path(__file__).resolve().parents[1]/'data'/'certificates')
    args=parser.parse_args()
    b=tuple(args.parameters); n=len(b)
    if not 2<=n<=10 or any(v<1 for v in b) or args.dilation<0:
        parser.error('Use 2..10 positive parameters and a nonnegative dilation.')
    x=tuple(v-1 for v in b)
    mu=[Fraction(evaluate(read_poly(args.certificates/f'magic_{n:02d}_{j:02d}.json'),x),factorial(n))
        for j in range(n+1)]
    ehr=[sum((mu[j]*comb(n-j,k-j) for j in range(k+1)),Fraction(0)) for k in range(n+1)]
    def count(t:int)->int:
        result=sum((c*t**k for k,c in enumerate(ehr)),Fraction(0))
        if result.denominator!=1:
            raise ArithmeticError('Nonintegral lattice count')
        return result.numerator
    hstar=[sum((-1)**(j-i)*comb(n+1,j-i)*count(i) for i in range(j+1)) for j in range(n+1)]
    print(json.dumps({'parameters':b,'coefficient_order':'ascending powers',
        'ehrhart':[str(c) for c in ehr], 'magic':[str(c) for c in mu],
        'h_star':hstar,'dilation':args.dilation,'lattice_count':count(args.dilation),
        'magic_positive':all(c>=0 for c in mu)},indent=2))

if __name__=='__main__':
    main()
