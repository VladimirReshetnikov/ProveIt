#!/usr/bin/env python3
"""Exact finite symbolic checks, distinct from the article's asymptotic proof."""
from __future__ import annotations
import sys
sys.dont_write_bytecode=True
import argparse
from fractions import Fraction
from math import factorial
import sympy as s
from common import emit, integer, new_file_path, require

MAX_ORDER=4


def contractions(order):
    """Finite weighted Gaussian algorithm E_order; bounded at order four."""
    integer(order,0,MAX_ORDER,'coefficient order')
    def parts(left,j,last):
        if j>last:
            if left==0:yield ()
            return
        for count in range(left//(j-2)+1):
            for rest in parts(left-(j-2)*count,j+1,last):yield ((j,count),)+rest
    out=[]
    for counts in parts(2*order,3,2*order+2):
        counts=tuple((j,k) for j,k in counts if k)
        degree=sum(j*k for j,k in counts)
        require(degree%2==0,'Gaussian contraction degree must be even')
        moment=1
        for j in range(1,degree,2):moment*=j
        coefficient=Fraction((-1)**(degree//2)*moment)
        for j,k in counts:coefficient/=factorial(j)**k*factorial(k)
        out.append((counts,degree//2,coefficient))
    return tuple(out)


def e_polynomial(order):
    integer(order,0,MAX_ORDER,'coefficient order')
    b=s.Symbol('b'); kappas={j:s.Symbol('k'+str(j)) for j in range(3,2*order+3)}
    return s.expand(sum(s.Rational(c.numerator,c.denominator)*s.prod(kappas[j]**k for j,k in ks)/b**bp for ks,bp,c in contractions(order)))


def _independent_gaussian(order):
    # Expand exp(sum k_j*(i*x)^j*h^(j-2)/j!) first, then integrate monomials.
    # This does not call the weighted-composition enumeration above.
    h,x,b=s.symbols('h x b',positive=True)
    phase=sum(s.Symbol('k'+str(j))*s.I**j*x**j*h**(j-2)/s.factorial(j) for j in range(3,2*order+3))
    poly=s.Poly(s.expand(sum(phase**k/s.factorial(k) for k in range(2*order+1))),h)
    coefficient=s.Poly(poly.coeff_monomial(h**(2*order)),x)
    result=0
    for (degree,),value in coefficient.terms():
        if degree%2==0:result+=value*s.factorial2(degree-1)/s.Symbol('b')**(degree//2)
    return s.expand(result)


def inverse_coefficients():
    """Finite formal reversal through relative L^-3, with ell=log L and c=log 2."""
    t,ell,c=s.symbols('t ell c');aa=s.symbols('a0:3')
    trunc=lambda x,n:s.series(x,t,0,n).removeO().expand()
    R=1/t+sum(aa[j]*t**j for j in range(3))
    logR=ell+trunc(s.log(t*R),4)
    invR=trunc(1/R,4)
    g=R+2*logR-c-1+3*invR-4*trunc(invR**2,4)+s.Rational(20,3)*trunc(invR**3,4)
    equation=trunc(R+3*logR-c+trunc(s.log(1+2*invR),3)+ell+trunc(s.log(trunc(t*g,4)),3)-1/t,3)
    sol={}
    for j in range(3):
        coefficient=s.expand(equation.subs(sol)).coeff(t,j)
        require(s.diff(coefficient,aa[j])==1,'inverse recursion lost its unit pivot')
        sol[aa[j]]=s.expand(-coefficient.subs(aa[j],0))
    qpoly=trunc(1/trunc(t*g.subs(sol),4),4)
    q=[s.expand(qpoly.coeff(t,j)) for j in range(4)]
    expected=[1,2*ell+1,4*ell**2-2*ell+c-1,
              8*ell**3-22*ell**2+8*c*ell-c-c**2/2-s.Rational(1,2)]
    require(all(s.expand(x-y)==0 for x,y in zip(q,expected)),'inverse coefficients mismatch')
    require(s.expand(equation.subs(sol))==0,'inverse saddle substitution residual')
    return {'r_coefficients_a0_a1_a2':[str(sol[x]) for x in aa],
            'relative_inverse_q0_q1_q2_q3':[str(x) for x in q],
            'equation_residual_through_t2':'0'}


def verify():
    b,k3,k4,k5,k6=s.symbols('b k3 k4 k5 k6')
    displayed=[s.Integer(1),k4/(8*b**2)-5*k3**2/(24*b**3),
    -k6/(48*b**3)+7*k3*k5/(48*b**4)+35*k4**2/(384*b**4)-35*k3**2*k4/(64*b**5)+385*k3**4/(1152*b**6)]
    for order in range(3):
        require(s.expand(e_polynomial(order)-displayed[order])==0,'displayed E coefficient mismatch')
        require(s.expand(_independent_gaussian(order)-displayed[order])==0,'independent Gaussian expansion mismatch')
    # Verify the derivative polynomials by direct differentiation, not their recurrence.
    z=s.Symbol('z');H=z**2*s.exp(z)/2;P=s.Integer(1);actual=H
    polynomials=[]
    for j in range(9):
        require(s.simplify(actual-H*P)==0,'cumulant polynomial recursion mismatch')
        polynomials.append(str(P));P=s.expand((z+2)*P+z*s.diff(P,z));actual=z*s.diff(actual,z)
    # Exact marked first/second Boltzmann derivatives of the component marker EGF.
    u,v,w,z=s.symbols('u v w z')
    marked=u*(v*z+z**3/s.Integer(6)+z**4/s.Integer(4)+v*z**4/s.Integer(6)+v**2*z**4/s.Integer(24))
    D=lambda f,a:a*s.diff(f,a)
    require(s.expand(D(marked,v).subs({u:1,v:1})-(z+z**4/4))==0,'defect mean polynomial')
    require(s.expand(D(D(marked,v),v).subs({u:1,v:1})-(z+z**4/3))==0,'defect variance polynomial')
    require(s.expand(D(D(marked,v),z).subs({u:1,v:1})-(z+z**4))==0,'size-defect covariance polynomial')
    return {'status':'PASS','E0_E1_E2':[str(x) for x in displayed],
            'independent_gaussian_expansion':'identical through weighted degree four',
            'bounded_algorithm_term_counts':{str(j):len(contractions(j)) for j in range(MAX_ORDER+1)},
            'cumulant_derivative_polynomials_P0_through_P8':polynomials,
            'inverse':inverse_coefficients(),
            'marked_polynomials':{'d':'r+r^4/4','tau_squared':'r+r^4/3','eta':'r+r^4'},
            'scope':'Exact finite coefficient and identity checks; not an analytic remainder proof, effective onset, or integer-threshold certificate.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output');args=parser.parse_args()
    if args.output is not None:new_file_path(args.output)
    emit(verify(),args.output)

if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
