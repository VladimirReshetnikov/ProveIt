"""Generate a compact exact polygamma identity from an order-eight inverse row.

The output encodes K(N), W(x)=K(x+1/2)-K(x-1/2), the explicit subtraction
polynomial S(x), and the exact value scale*zeta(2k). The associated ordinary
sum is sum_n [W(n+1/2)*A_8(n)*A_(2b)(n)-S(n+1/2)].
"""
from __future__ import annotations
import argparse
from functools import reduce
import json
import math
from pathlib import Path
import sympy as sp


def source_matrix(b):
    def entry(i,k):
        index=2*i+2*k-6
        if index<0:
            return sp.S.Zero
        total=sp.S.Zero
        for upper,lower in [(2*i+2,8-2*k),(2*b+2*i-6,2*b-2*k)]:
            if 2<=lower<=upper:
                total+=sp.binomial(upper,lower)/upper
        return sp.bernoulli(index)*total
    return sp.Matrix(b,b,entry)


def centered_tail_coefficient(order,j):
    if j==0:
        return sp.Rational(1,order-1)
    return sp.rf(order,2*j-1)*sp.bernoulli(2*j,sp.Rational(1,2))/sp.factorial(2*j)


def generate(b,k):
    assert b>=5 and 0<=k<b
    M=source_matrix(b)
    target=sp.zeros(b,1);target[k]=1
    inverse_row=M.T.inv()*target
    denominator=sp.ilcm(*(value.q for value in inverse_row))
    integers=[int(value*denominator) for value in inverse_row]
    divisor=reduce(math.gcd,map(abs,integers))
    integers=[v//divisor for v in integers]
    scale=sp.Rational(denominator,divisor)
    row=sp.Matrix(1,b,integers)
    assert row*M==scale*target.T
    # Independent centered-difference coefficient construction.
    coefficients={2*r:sp.S.Zero for r in range(2*b)}
    for t,coefficient in enumerate(integers):
        j=b+t
        for r in range(j+1):
            coefficients[2*r]+=coefficient*sp.binomial(2*j+1,2*r)*sp.Rational(1,2)**(2*(j-r))
    # Product tail begins at x^(-2b-6); only b-3 subtraction coefficients are possible.
    c=[sum(centered_tail_coefficient(8,j)*centered_tail_coefficient(2*b,ell-j)
           for j in range(ell+1)) for ell in range(b-3)]
    subtraction={2*d:sp.S.Zero for d in range(b-3)}
    for power,w in coefficients.items():
        for ell,tail in enumerate(c):
            exponent=power-2*b-6-2*ell
            if exponent>=0:
                subtraction[exponent]+=w*tail
    K={2*(b+t)+1:str(v) for t,v in enumerate(integers)}
    return {'b':b,'p':8,'q':2*b,'zeta_coordinate_index':k,
            'identity':'sum_n>=0 [W(n+1/2)*psi^(7)(n+1)*psi^(2b-1)(n+1)/(7!*(2b-1)!)-S(n+1/2)] = scale*zeta(2k)',
            'K_coefficients_by_exponent':K,
            'W_definition':'K(x+1/2)-K(x-1/2)',
            'S_coefficients_by_exponent':{str(power):str(v) for power,v in subtraction.items()},
            'scale':str(scale),'evaluated_rhs_if_rational':str(-scale/2) if k==0 else None,
            'ordinary_convergence':'After these exact subtractions the summand is O(n^-2).',
            'all_exact_coordinate_cancellations_passed':True,
            'primitive_integer_row_gcd':reduce(math.gcd,map(abs,integers))}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--b',type=int,default=17)
    parser.add_argument('--k',type=int,default=0)
    parser.add_argument('--output',type=Path,default=None)
    args=parser.parse_args()
    out=args.output or Path(__file__).with_name(f'order8_identity_b{args.b}_k{args.k}.json')
    result=generate(args.b,args.k)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'output':str(out),'terms_in_K':len(result['K_coefficients_by_exponent']),
                      'terms_in_S':len(result['S_coefficients_by_exponent']),
                      'bytes':out.stat().st_size,'all_exact_checks_passed':True},indent=2))

if __name__=='__main__':
    main()
