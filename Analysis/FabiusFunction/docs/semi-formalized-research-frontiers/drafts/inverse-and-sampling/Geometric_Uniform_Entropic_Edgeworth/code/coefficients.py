#!/usr/bin/env python3
"""Exact entropy/finite-order Renyi coefficients for geometric uniform sums.

No floating-point arithmetic is used. Coefficients are algebraic checks, not
machine verification of the analytic remainder theorem in the article.
Run: python code/coefficients.py --order 8 --output data
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as sp

EPS, Z, X, ALPHA = sp.symbols('epsilon z x alpha')


def gaussian_expectation(poly: sp.Poly) -> sp.Expr:
    """Integrate a polynomial against the standard normal density exactly."""
    result = sp.S.Zero
    for (degree,), coefficient in poly.terms():
        if degree % 2 == 0:
            moment = sp.factorial(degree) / (2**(degree//2)*sp.factorial(degree//2))
            result += coefficient * moment
    return sp.expand(result)


def compute(order: int) -> dict:
    if order < 2 or order > 14:
        raise ValueError('Choose an order between 2 and 14; high orders can be slow.')
    # D_N only requires P_1,...,P_(N-1), since its linear term vanishes.
    top = order - 1
    q = 1 - EPS
    log_series = sp.S.Zero
    cumulants = {}
    for r in range(2, top + 2):
        constant = sp.Rational(3**r * 2**(2*r), 2*r) * sp.bernoulli(2*r)
        lam = constant * (1-q*q)**(r-1) / sum(q**(2*j) for j in range(r))
        series = sp.series(lam, EPS, 0, top+1).removeO().expand()
        cumulants[str(2*r)] = str(series)
        log_series += series * Z**(2*r) / sp.factorial(2*r)
    log_series = sp.Poly(log_series, EPS)
    A = [sp.Poly(0, Z)] + [sp.Poly(log_series.nth(j), Z) for j in range(1, top+1)]
    E = [sp.Poly(1, Z)]
    for n in range(1, top+1):
        total = sp.Poly(0, Z)
        for j in range(1, n+1):
            total += j*A[j]*E[n-j]
        E.append(total.mul_ground(sp.Rational(1,n)))
    P = [sp.Poly(0, X)]
    for n in range(1, top+1):
        P.append(sp.Poly(sum(c*sp.hermite_prob(k, X)
                            for (k,), c in E[n].terms()), X))
        assert gaussian_expectation(P[n]) == 0
        assert gaussian_expectation(P[n]*sp.Poly(X**2, X)) == 0
    # Exact coefficients of E[U^k], U=sum epsilon^j P_j.
    products = {(1,n): P[n] for n in range(1,top+1)}
    moments = {}
    for k in range(2, order+1):
        for n in range(k, order+1):
            total = sp.Poly(0, X)
            for j in range(1,min(top,n-k+1)+1):
                previous = products.get((k-1,n-j))
                if previous is not None:
                    total += P[j]*previous
            products[k,n] = total
            moments[k,n] = gaussian_expectation(total)
    kl = {}
    for n in range(2,order+1):
        kl[n] = sp.factor(sum(sp.Rational((-1)**k,k*(k-1))*moments[k,n]
                              for k in range(2,n+1)))
    renyi_m = {0:sp.S.One,1:sp.S.Zero}
    log_m = {0:sp.S.Zero,1:sp.S.Zero}
    renyi = {}
    for n in range(2,order+1):
        value = sp.S.Zero
        for k in range(2,n+1):
            falling = sp.prod(ALPHA-j for j in range(k))/sp.factorial(k)
            value += falling*moments[k,n]
        renyi_m[n] = sp.expand(value)
        log_m[n] = sp.expand(renyi_m[n] - sum(j*log_m[j]*renyi_m[n-j]
                                               for j in range(1,n))/n)
        renyi[n] = sp.cancel(log_m[n]/(ALPHA-1)).expand()
        assert sp.Poly(renyi[n], ALPHA).degree() <= n-1
        assert sp.simplify(renyi[n].subs(ALPHA,1)-kl[n]) == 0
        assert sp.simplify(renyi[n].subs(ALPHA,0)) == 0
    assert kl[2] == sp.Rational(3,100)
    if order >= 3:
        assert kl[3] == sp.Rational(33,500)
    return {'order': order,
            'kl':{str(n):str(kl[n]) for n in kl},
            'renyi':{str(n):str(renyi[n]) for n in renyi},
            'hermite_symbol_polynomials':{str(n):str(E[n].as_expr()) for n in range(1,top+1)},
            'ordinary_polynomials':{str(n):str(P[n].as_expr()) for n in range(1,top+1)},
            'cumulant_series':cumulants,
            'gaussian_product_moments':{f'{k},{n}':str(v) for (k,n),v in moments.items()},
            'checks':'All normalization, variance, alpha=1, alpha=0 and leading-coefficient assertions passed.'}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=int,default=8)
    parser.add_argument('--output',type=Path,default=Path('data'))
    args=parser.parse_args()
    result=compute(args.order)
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'exact_coefficients.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    text='Exact KL coefficients d_n in epsilon=1-q\n'
    for n,value in result['kl'].items():
        text+=f'd_{n} = {value} = {sp.N(sp.sympify(value),18)}\n'
    text+='\nRenyi coefficients (alpha is the fixed divergence order)\n'
    for n,value in result['renyi'].items(): text+=f'd_{n}(alpha) = {value}\n'
    text+='\n'+result['checks']+'\n'
    (args.output/'coefficients.txt').write_text(text,encoding='utf-8')
    print(text)

if __name__=='__main__':
    main()
