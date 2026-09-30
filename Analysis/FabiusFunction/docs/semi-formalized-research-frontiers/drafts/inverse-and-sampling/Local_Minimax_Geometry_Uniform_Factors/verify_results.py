#!/usr/bin/env python3
"""Reproducible algebraic checks and optional high-precision likelihood checks.

These checks support, but do not replace, the proofs in article.tex.
Usage: python verify_results.py [--numerics] [--output PATH]
Dependencies: sympy; mpmath (for --numerics).
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as sp


def power_sum(nodes: list[sp.Expr], k: int) -> sp.Expr:
    return sp.expand(sum(x**k for x in nodes))


def exact_checks() -> dict:
    count = 0
    # General shifted-moment tangent: dp_k/dt = 0 up to the first omitted order.
    for r in range(1, 9):
        nodes = [sp.Integer(i) for i in range(1, r + 1)]
        for ell in range(4):
            weights = [1 / (x**ell * sp.prod(x-y for y in nodes if y != x))
                       for x in nodes]
            for k in range(ell + 1, ell + r):
                assert sp.simplify(k * sum(x**(k-1)*w for x,w in zip(nodes,weights))) == 0
                count += 1
            k = ell + r
            assert sp.simplify(k * sum(x**(k-1)*w for x,w in zip(nodes,weights))) == k
            count += 1
            if ell == 1:
                assert sp.simplify(sum(weights)) == (-1)**(r+1)/sp.prod(nodes)
                count += 1
    # Exact hard pairs for a two-factor zero block.
    alpha, beta = [sp.Integer(1),sp.Integer(8)], [sp.Integer(4),sp.Integer(7)]
    assert power_sum(alpha,2) == power_sum(beta,2) == 65
    assert power_sum(alpha,1)-power_sum(beta,1) == -2
    assert power_sum(alpha,3)-power_sum(beta,3) == 106
    count += 3
    known_alpha, known_beta = [sp.Integer(1),sp.Integer(4)], [sp.Integer(2),sp.Integer(3)]
    assert power_sum(known_alpha,1) == power_sum(known_beta,1) == 5
    assert power_sum(known_alpha,2)-power_sum(known_beta,2) == 4
    count += 2
    # The positivity certificate for a mixed base with two zeros.
    z,s = sp.symbols('z s')
    E = (1+z)**2 * (1+3*z)
    coeff = sp.expand(E * sum((s*z)**j/sp.factorial(j) for j in range(7))).coeff(z,6)
    expected = s**3/sp.Integer(2)+7*s**4/sp.Integer(24)+s**5/sp.Integer(24)+s**6/sp.Integer(720)
    assert sp.expand(coeff-expected) == 0
    count += 1
    # Newton sums remain fixed under a change of the constant coefficient.
    x,t = sp.symbols('x t')
    for q in range(1,8):
        P = sp.Poly(sp.prod(x-i for i in range(1,q+1)) + t,x)
        coeffs = P.all_coeffs()[1:]
        p = {}
        for k in range(1,q+1):
            p[k] = sp.expand(-sum(coeffs[j-1]*p[k-j] for j in range(1,k)) - k*coeffs[k-1])
            if k < q:
                assert sp.diff(p[k],t) == 0
            else:
                assert sp.diff(p[k],t) == -q
            count += 1
    unknown_chi = sp.factorial(6)*(sp.Rational(106,2835))**2
    known_chi = sp.factorial(4)*sp.Rational(1,45)**2
    return {
        'exact_assertions_passed':count,
        'unknown_pair_squared_scales': [[1,8],[4,7]],
        'unknown_pair_power_sum_differences':[-2,0,106],
        'mixed_base_missing_p1_certificate':str(expected),
        'unknown_r2_gaussian_chi2_over_h12_limit':str(unknown_chi),
        'unknown_r2_gaussian_H2_over_h12_limit':str(unknown_chi/4),
        'known_r2_gaussian_chi2_over_h8_limit':str(known_chi),
        'known_r2_gaussian_H2_over_h8_limit':str(known_chi/4),
    }


def numerical_checks() -> list[dict]:
    import mpmath as mp
    mp.mp.dps = 65
    def phi(x):
        return mp.exp(-x*x/2)/mp.sqrt(2*mp.pi)
    def Phi(x):
        return mp.erfc(-x/mp.sqrt(2))/2
    def density(y,a,b,v):
        sigma=mp.sqrt(v)
        def G(t):
            return t*Phi(t/sigma)+sigma*phi(t/sigma)
        return (G(y+a+b)-G(y+a-b)-G(y-a+b)+G(y-a-b))/(4*a*b)
    rows=[]
    # Finite integration range; this is high-precision corroboration, not interval certification.
    for hs in ('0.12','0.09','0.06','0.04'):
        h=mp.mpf(hs)
        def f(y):
            return density(y,h,h*mp.sqrt(8),1-3*h*h)
        def g(y):
            return density(y,2*h,h*mp.sqrt(7),1-mp.mpf(11)*h*h/3)
        def chi_integrand(y):
            fy,gy=f(y),g(y)
            return (fy-gy)**2/gy
        def h_integrand(y):
            fy,gy=f(y),g(y)
            return (fy-gy)**2/(mp.sqrt(fy)+mp.sqrt(gy))**2
        # Even densities; integrate only the positive half.
        chi=2*mp.quad(chi_integrand,[0,1,2,3,4,6,8,10,12])
        h2=2*mp.quad(h_integrand,[0,1,2,3,4,6,8,10,12])
        rows.append({'h':hs,'chi2_over_h12':mp.nstr(chi/h**12,16),
                     'H2_over_h12':mp.nstr(h2/h**12,16)})
    return rows


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--numerics',action='store_true',
                        help='also run 65-digit finite-window likelihood diagnostics')
    parser.add_argument('--output',type=Path,
                        default=Path(__file__).with_name('verification_results.json'),
                        help='JSON output path (parent directories are created)')
    args=parser.parse_args()
    if not __debug__:
        parser.error('run without -O: the exact checks require Python assertions')
    result=exact_checks()
    if args.numerics:
        result['numerical_likelihood_checks']=numerical_checks()
    output=args.output
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
