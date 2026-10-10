#!/usr/bin/env python3
"""Finite exact Gaussian-moment compiler for saddle corrections.

This verifies the normalization against the pure-gamma model and exports
the first three correction formulas as exact symbolic expressions.
"""
from pathlib import Path
from itertools import product
import json
import sympy as sp


def laplace_coefficient(j):
    B = sp.Symbol('B', positive=True)
    f = [sp.Integer(1)] + [sp.Symbol(f'f{r}') for r in range(1, 2*j+1)]
    b = {m: sp.Symbol(f'b{m}') for m in range(3, 2*j+3)}
    answer = sp.Integer(0)
    ms = list(b)
    ranges = [range(2*j//(m-2)+1) for m in ms]
    for counts in product(*ranges):
        order = sum((m-2)*k for m,k in zip(ms,counts))
        if order > 2*j:
            continue
        r = 2*j-order
        degree = r+sum(m*k for m,k in zip(ms,counts))
        assert degree % 2 == 0
        term = f[r]/sp.factorial(r)
        for m,k in zip(ms,counts):
            term *= b[m]**k/(sp.factorial(m)**k*sp.factorial(k))
        moment = sp.factorial2(degree-1)/B**(degree//2) if degree else 1
        answer += term*moment
    return sp.expand(answer)


def compile_coefficients(order=3):
    eps=sp.Symbol('eps')
    cs=[laplace_coefficient(j) for j in range(order+1)]
    inverse_star=sp.series(sp.exp(-sum(
        sp.bernoulli(2*r)*eps**(2*r-1)/(2*r*(2*r-1))
        for r in range(1,(order+1)//2+1))),eps,0,order+1).removeO()
    ds=[sp.expand(sum(cs[k]*inverse_star.coeff(eps,j-k)
                      for k in range(j+1))) for j in range(order+1)]
    B=sp.Symbol('B',positive=True)
    pure={B:1}
    pure.update({sp.Symbol(f'f{r}'):(-1)**r*sp.factorial(r)
                 for r in range(1,2*order+1)})
    pure.update({sp.Symbol(f'b{m}'):(-1)**(m-1)*sp.factorial(m-1)
                 for m in range(3,2*order+3)})
    gamma_values=[sp.simplify(c.subs(pure)) for c in cs]
    corrected=[sp.simplify(d.subs(pure)) for d in ds]
    assert gamma_values == [1,sp.Rational(1,12),sp.Rational(1,288),
                            -sp.Rational(139,51840)][:order+1]
    assert corrected == [1]+[0]*order
    expected_d1=(sp.Symbol('f2')/(2*B)+sp.Symbol('b3')*sp.Symbol('f1')/(2*B**2)
                 +sp.Symbol('b4')/(8*B**2)+5*sp.Symbol('b3')**2/(24*B**3)
                 -sp.Rational(1,12))
    assert sp.expand(ds[1]-expected_d1) == 0
    return cs,ds,gamma_values


def main():
    cs,ds,pure=compile_coefficients()
    out=Path(__file__).resolve().parent.parent/'results'
    out.mkdir(parents=True,exist_ok=True)
    report={'status':'exact symbolic compiler checks passed',
            'conventions':'fr=g^(r)(1)/g(1), bm=phi^(m)(1), B=-phi^(2)(1)',
            'c':[str(c) for c in cs], 'd':[str(d) for d in ds],
            'pure_gamma_c':[str(x) for x in pure],
            'pure_gamma_d':['1','0','0','0']}
    (out/'saddle_coefficients.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'])
    print('c0..c3 in pure-gamma model:', ', '.join(map(str,pure)))
    print('d1, d2, d3 terms:', *[len(sp.Add.make_args(d)) for d in ds[1:]])


if __name__=='__main__':
    main()
