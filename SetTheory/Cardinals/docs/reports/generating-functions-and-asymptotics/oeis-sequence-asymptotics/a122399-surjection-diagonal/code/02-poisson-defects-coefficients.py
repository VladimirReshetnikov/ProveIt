#!/usr/bin/env python3
"""Exact boundary expansion coefficients for the A122399 rectangular family.

Run from the package root: python code/coefficients.py --order 4
Requires SymPy. No coefficients are fitted to numerical sequence data.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as sp

j, r, lam, v, z = sp.symbols('j r lambda v z')

def generate(order: int):
    if not 0 <= order <= 8:
        raise ValueError('order must be between 0 and 8')
    # Bernoulli formula: log((exp(z)-1)/z)=z/2+sum B_(2k)z^(2k)/(2k(2k)!).
    ell = {1: sp.Rational(1, 2)}
    for h in range(2, order + 2):
        ell[h] = sp.bernoulli(h) / (h * sp.factorial(h)) if h % 2 == 0 else 0
    E = {}
    for h in range(1, order + 1):
        E[h] = (2**(h + 1) * ell.get(h + 1, 0) * v**(h + 1)
                - j * 2**h * ell.get(h, 0) * v**h
                - r * j**(h + 1) / (h + 1))
    B = [sp.Integer(1)]
    for h in range(1, order + 1):
        B.append(sp.expand(sum(k * E[k] * B[h-k] for k in range(1, h+1))/h))
    P = [sp.expand(sum(c * sp.ff(j, p[0]) for p, c in sp.Poly(b, v).terms())) for b in B]
    C = [sp.expand(sum(c * sp.bell(p[0], lam) for p, c in sp.Poly(pj, j).terms())) for pj in P]
    L = [sp.Integer(0)]
    for h in range(1, order + 1):
        L.append(sp.expand(C[h]-sum(k*L[k]*C[h-k] for k in range(1,h))/h))
    return P, C, L

def inverse_first_two(L):
    beta, ell = sp.symbols('beta ell')
    d0 = sp.cancel(L[1]/lam).subs({lam: beta, r: ell})
    d1 = sp.expand(d0**2/2 + (d0*(sp.diff(L[1],r)-lam*sp.diff(L[1],lam))/lam
                              + L[2]/lam).subs({lam: beta, r: ell}))
    return beta, ell, sp.expand(d0), sp.expand(d1)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--order', type=int, default=4)
    args = ap.parse_args()
    root = Path(__file__).resolve().parents[1]
    (root/'data').mkdir(exist_ok=True)
    P, C, L = generate(args.order)
    out = {name: [str(q) for q in vals] for name, vals in [('P',P),('C',C),('L',L)]}
    if args.order >= 2:
        beta, ell, d0, d1 = inverse_first_two(L)
        out['inverse'] = {'d0':str(d0), 'd1':str(d1)}
    (root/'data'/'coefficients.json').write_text(json.dumps(out,indent=2)+'\n')
    lines = []
    for h in range(args.order+1):
        lines.extend([f'P_{h} = {sp.factor(P[h])}',f'C_{h} = {sp.factor(C[h])}'])
        if h:
            lines.append(f'L_{h} = {sp.collect(L[h],lam)}')
    if args.order>=2:
        lines.extend(['d0 = '+str(d0),'d1 = '+str(sp.collect(d1,beta))])
    (root/'data'/'coefficients.txt').write_text('\n\n'.join(lines)+'\n')
    print('\n'.join(lines[-5:]))
    print('Exact rational coefficients written through order',args.order)

if __name__ == '__main__':
    main()
