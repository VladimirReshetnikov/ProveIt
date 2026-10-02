#!/usr/bin/env python3
"""Derive critical-scale coefficients exactly from Bernoulli power sums.

Usage: python derive_coefficients.py --order 5
Higher orders are supported algebraically but can be expensive. Output files
are overwritten beside this script. Requires SymPy.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parent

def derive(order: int) -> tuple[list[s.Expr], list[s.Expr]]:
    if order < 1:
        raise ValueError('order must be positive')
    x, c, m, j = s.symbols('x c m j', positive=True)
    power_sums = {r: s.summation(j**(2*r), (j, 1, m)).expand()
                  for r in range(1, order+1)}
    gamma = {r: -s.bernoulli(2*r)*power_sums[r]/(2*r*s.factorial(2*r))
             for r in power_sums}
    a = [s.Integer(1)]
    for k in range(1, order+1):
        a.append(s.expand(sum(r*gamma[r]*a[k-r] for r in range(1,k+1))/k))
    def trunc(expr: s.Expr) -> s.Expr:
        return s.series(expr, x, 0, order+1).removeO().expand()
    Q = s.Integer(1)
    h = (x+x*x)/(4*c)
    for k in range(1,order+1):
        pol = s.expand(a[k].subs(m,1/x)*x**(4*k)
                       *s.prod(1-i*x for i in range(1,2*k+1))/c**(2*k))
        Q += trunc(pol*sum(s.binomial(-2*k,r)*h**r
                            for r in range(order+1-k)))
    U = trunc(Q)-1
    logQ = trunc(sum((-1)**(r+1)*U**r/s.Integer(r)
                     for r in range(1,order+1)))
    shift = trunc((1/x-1)*sum((-1)**(r+1)*h**r/s.Integer(r)
                              for r in range(1,order+3)))
    stirling = -sum(2*s.bernoulli(2*r)/(2*r*(2*r-1))*x**(2*r-1)
                    for r in range(1,(order+1)//2+1))
    L = trunc(logQ+shift-1/(4*c)+stirling)
    logs = [s.factor(L.coeff(x,i)) for i in range(1,order+1)]
    relative = [s.Integer(1)]
    for k in range(1,order+1):
        relative.append(s.factor(sum(i*logs[i-1]*relative[k-i]
                                     for i in range(1,k+1))/k))
    return logs, relative

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--order', type=int, default=5)
    args = p.parse_args()
    logs, relative = derive(args.order)
    data = {'log':[str(v) for v in logs], 'relative':[str(v) for v in relative]}
    (ROOT/'coefficients.json').write_text(json.dumps(data,indent=2)+'\n')
    (ROOT/'coefficients_tex.txt').write_text('\n'.join(
        f'L_{{{i}}}(c)&={s.latex(v)}\\\\' for i,v in enumerate(logs,1))+'\n')
    for i,v in enumerate(logs,1): print(f'L_{i}(c) = {v}')

if __name__ == '__main__':
    main()
