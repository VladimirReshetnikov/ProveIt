#!/usr/bin/env python3
"""Finite, exact generation of all-order joint-moment correction polynomials.

The algorithm implements equation (polynomial-prescription) in
../../sections/04-joint-moments.tex.
It expands in the formal variable 1/m first. It never sums the divergent
fixed-m residue series. By default it emits generic P0,...,P3 using symbols
delta, g_1,...,g_3, h_2,...,h_4, where g=log Gamma(1+x) and
H=g+log(log Gamma(1-x)/(gamma*x)).
"""
import argparse
import json
from pathlib import Path
import sympy as s


def generate(order):
    t,l,w,j,delta=s.symbols('t lambda w j delta')
    gs=s.symbols('g1:'+str(order+1))
    hs=s.symbols('h2:'+str(order+2))
    a=[s.Integer(0)]
    for k in range(1,order+1):
        theta=t*(-1)**(k+1)*sum(s.binomial(k-1,r-1)*j**(r+1)/s.Integer(r+1) for r in range(1,k+1))
        a.append(hs[k-1]*w**(k+1)+(j+1)*gs[k-1]*w**k+theta)
    b=[s.Integer(1)]
    for k in range(1,order+1):
        b.append(s.Poly(s.expand(sum(r*a[r]*b[k-r] for r in range(1,k+1))/k),w,j).as_expr())
    polynomials=[]
    for k,expr in enumerate(b):
        p=0
        for (power_w,power_j),coefficient in s.Poly(expr,w,j).terms():
            # exp(-delta*l) D^p [l^d exp(delta*l)] = (D+delta*l)^p l^d.
            q=l**power_w
            for _ in range(power_j):q=s.expand(l*s.diff(q,l)+delta*l*q)
            p+=coefficient*q
        p=s.expand(p)
        assert s.degree(p,t)<=k
        assert s.degree(p,l)<=2*k
        touchard=s.Integer(1)
        for _ in range(2*k):
            touchard=s.expand(l*s.diff(touchard,l)+delta*l*touchard)
        assert s.expand(p.coeff(t,k)-touchard/(2**k*s.factorial(k)))==0
        if k:
            highest=(hs[0]+gs[0]*delta+t*delta**2/2)**k/s.factorial(k)
            assert s.expand(p.coeff(l,2*k)-highest)==0
        polynomials.append(p)
    return polynomials


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--order',type=int,default=3)
    args=parser.parse_args()
    if args.order<0:raise ValueError('order must be nonnegative')
    ps=generate(args.order)
    here=Path(__file__).resolve().parent
    records=[]
    for k,p in enumerate(ps):
        records.append({'order':k,'sympy':str(p),'latex':s.latex(p)})
        print('P'+str(k)+': exact polynomial; '+str((len(s.Poly(p,*sorted(p.free_symbols,key=str)).terms()) if p.free_symbols else 1))+' monomials')
    (here/'transition_polynomials.json').write_text(json.dumps(records,indent=2)+'\n')
    print('PASS: all degree bounds and both extremal-coefficient identities verified.')

if __name__=='__main__':main()
