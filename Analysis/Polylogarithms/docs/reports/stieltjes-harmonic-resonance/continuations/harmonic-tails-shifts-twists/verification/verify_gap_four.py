#!/usr/bin/env python3
"""Exact certificates for gap-four tail ranks and negative order-two minors.

All matrix, recurrence, inverse, and identity checks use rational arithmetic.
Finite checks supplement the proofs in gap_four.tex; they are not an
all-order proof. Run with Python 3 and SymPy: python verify_gap_four.py.
"""
import argparse
import json
from functools import lru_cache
from math import gcd
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parent

@lru_cache(None)
def alpha(n):
    assert n >= 1
    return 2 * abs(sp.bernoulli(2*n)) / sp.factorial(2*n)


def factors(c, s):
    aa = sp.Integer(0) if s <= c else sp.factorial(2*s)/sp.factorial(2*s-2*c)
    bb = sp.Integer(0) if s <= c else sp.factorial(2*s-1)/sp.factorial(2*s-2*c-1)
    return aa, bb, 2*(aa+bb)


def kernel(c, s, u):
    assert s > c and 1 <= u < s
    au = factors(c, u)[0]
    aa, bb, dd = factors(c, s)
    return alpha(s-u)*(bb+au)/dd


def fundamental(c, last):
    rr = [[sp.Integer(0)]*c]
    rr += [[sp.Integer(s==j) for j in range(1,c+1)] for s in range(1,c+1)]
    for s in range(c+1,last+1):
        rr.append([sum(kernel(c,s,u)*rr[u][j] for u in range(1,s))
                   for j in range(c)])
    return rr


def late_entry(p, q, j, k):
    dd = 2*j+1
    ee = dd-p-q+2*k+1
    if ee < 0:
        return sp.Integer(0)
    out = sp.Integer(0)
    for upper, lower in ((dd-q+1,p-2*k),(dd-p+1,q-2*k)):
        if 2 <= lower <= upper:
            out += sp.binomial(upper,lower)/upper
    return sp.bernoulli(ee)*out


def late_matrix(p,q):
    b = q//2
    return sp.Matrix([[late_entry(p,q,j,k) for k in range(b)]
                      for j in range(b,2*b)])


def direct_odd_coefficient_matrix(c,b):
    out = sp.zeros(b)
    for r in range(1,b+1):
        s = r+c
        aa,bb,dd = factors(c,s)
        for u in range(1,b+1):
            if u == s:
                out[r-1,u-1] = dd
            elif u < s:
                out[r-1,u-1] = -alpha(s-u)*(bb+factors(c,u)[0])
    return out


def centered_tail_coefficient(p,m):
    if m == 0:
        return sp.Rational(1,p-1)
    return sp.bernoulli(2*m,sp.Rational(1,2))*sp.rf(p,2*m-1)/sp.factorial(2*m)


def primitive_integer_rational_identity(p,q):
    b = q//2
    mat = late_matrix(p,q)
    inverse_first_row = mat.inv()[0,:]
    weights = []
    for r in range(q):
        weights.append(sum(inverse_first_row[j-b]*sp.binomial(2*j+1,2*r)
                           *sp.Rational(1,2)**(2*(j-r))
                           for j in range(max(b,r),q)))
    scale = sp.ilcm(*(a.q for a in weights))
    integers = [int(scale*a) for a in weights]
    common = 0
    for value in integers:
        common = gcd(common,abs(value))
    integers = [a//common for a in integers]
    rational_scale = sp.Rational(scale,common)
    if integers[-1] < 0:
        integers = [-a for a in integers]
        rational_scale = -rational_scale
    x = sp.Symbol('x')
    poly = sum(v*x**(2*r) for r,v in enumerate(integers))
    c = (q-p)//2
    product = [sum(centered_tail_coefficient(p,m)*centered_tail_coefficient(q,j-m)
                   for m in range(j+1)) for j in range(c+1)]
    subtraction = sp.expand(sum(integers[r]*product[j]*x**(2*r+2-p-q-2*j)
                               for r in range(q) for j in range(c+1)
                               if 2*r+2-p-q-2*j >= 0))
    return dict(weights=integers,rhs=str(-rational_scale/2),
                polynomial=str(poly),subtraction=str(subtraction),
                latex_polynomial=sp.latex(poly),latex_subtraction=sp.latex(subtraction),
                matrix=[[str(v) for v in row] for row in mat.tolist()],
                determinant=str(mat.det()))


def finite_telescoping_certificate(p,q):
    """Construct and verify an ordinary polynomial telescoping certificate.

    The odd polynomial K has primitive integer coefficients. Its centered
    difference can have rational coefficients, but no large common power
    of two is artificially introduced merely to clear those denominators.
    """
    b=q//2
    xx,nn,aa,bb=sp.symbols('x N A B')
    basic=primitive_integer_rational_identity(p,q)
    scale=-2*sp.Rational(basic['rhs'])
    coefficients=[scale*v for v in late_matrix(p,q).inv()[0,:]]
    common=sp.igcd(*(int(v) for v in coefficients))
    coefficients=[v/common for v in coefficients]
    kk=sum(v*nn**(2*j+1) for j,v in zip(range(b,q),coefficients))
    pp=sp.expand(kk.subs(nn,xx+sp.Rational(1,2))-kk.subs(nn,xx-sp.Rational(1,2)))
    ss=sp.sympify(basic['subtraction'],locals={'x':xx})/common
    rhs=sp.Rational(basic['rhs'])/common
    def antidifference(poly):
        return sp.expand(sum(value*(sp.bernoulli(power[0]+1,nn+1)
                                     -sp.bernoulli(power[0]+1))/(power[0]+1)
                             for power,value in sp.Poly(poly,nn).terms()))
    up=antidifference(sp.cancel(kk/nn**q))
    uq=antidifference(sp.cancel(kk/nn**p))
    delta_v=sp.cancel(kk/nn**(p+q)+up.subs(nn,nn-1)/nn**p
                      +uq.subs(nn,nn-1)/nn**q-ss.subs(xx,nn-sp.Rational(1,2)))
    assert delta_v.is_polynomial(nn)
    vv=antidifference(delta_v)
    def ff(n,a,b):
        return kk.subs(nn,n)*a*b+up.subs(nn,n)*a+uq.subs(nn,n)*b+vv.subs(nn,n)
    residual=sp.cancel(ff(nn,aa,bb)-ff(nn-1,aa+nn**(-p),bb+nn**(-q))
                       -pp.subs(xx,nn-sp.Rational(1,2))*(aa+nn**(-p))*(bb+nn**(-q))
                       +ss.subs(xx,nn-sp.Rational(1,2)))
    assert residual == 0
    def tail(order):
        return (sp.Rational(1,order-1)*nn**(1-order)-sp.Rational(1,2)*nn**(-order)
                +sum(sp.bernoulli(2*j)*sp.rf(order,2*j-1)/sp.factorial(2*j)
                     *nn**(1-order-2*j) for j in range(1,3)))
    t1,t2=tail(p),tail(q)
    large=sp.expand(ff(nn,t1,t2))
    nonnegative={power:large.coeff(nn,power) for power in range(0,6)}
    assert nonnegative[0] == rhs and all(nonnegative[power] == 0 for power in range(1,6))
    assert ff(0,aa,bb) == 0
    assert sp.Matrix([coefficients])*late_matrix(p,q) == sp.Matrix([[-2*rhs]+[0]*(b-1)])
    # Centered tails verify that the ordinary summand decays as O(n^-2).
    centered_product=sum(sum(centered_tail_coefficient(p,j)
                             *centered_tail_coefficient(q,m-j) for j in range(m+1))
                         *xx**(2-p-q-2*m) for m in range(3))
    expanded=sp.expand(pp*centered_product-ss)
    assert all(expanded.coeff(xx,power)==0 for power in range(0,5))
    return dict(p=p,q=q,K=str(sp.factor(kk)),K_coefficients=[str(v) for v in coefficients],
                centered_difference_P=str(pp),subtraction_S=str(sp.factor(ss)),rhs=str(rhs),
                U_p=str(sp.factor(up)),U_q=str(sp.factor(uq)),V=str(sp.factor(vv)),
                finite_difference_residual=str(residual),
                limit_nonnegative_coefficients={str(k):str(v) for k,v in nonnegative.items()},
                constant_contributions={"K_Ap_Aq":str(sp.expand(kk*t1*t2).coeff(nn,0)),
                                        "U_p_Ap":str(sp.expand(up*t1).coeff(nn,0)),
                                        "U_q_Aq":str(sp.expand(uq*t2).coeff(nn,0))})


def verify(output_path=None):
    results = {"arithmetic":"exact rational (SymPy)","gap_four":[],"order_two_minors":[]}
    # Independent Bernoulli-entry and differential-coefficient constructions.
    for b in range(3,19):
        c=2
        p,q=2*b-4,2*b
        mat=late_matrix(p,q)
        rr=fundamental(c,b+c)
        boundary=sp.Matrix([rr[b+1],rr[b+2]])
        determinant=mat.det(method='domain-ge')
        ee=rr[b+2][0]*rr[b+1][1]-rr[b+1][0]*rr[b+2][1]
        assert ee > 0 and boundary.det() == -ee
        factor=(-1)**(b*(b-1)//2)*sp.prod(factors(c,s)[2] for s in range(c+1,b+c+1))/(4**b*sp.factorial(b))
        assert determinant == factor*boundary.det()
        closed=(-1)**(b*(b-1)//2+1)*4**b*sp.factorial(b+1)**2*sp.factorial2(2*b+3)*sp.factorial2(2*b+1)*ee/(3*sp.factorial(b))
        assert determinant == closed
        hh=direct_odd_coefficient_matrix(c,b)
        col=sp.zeros(b)
        for u in range(1,b+1):
            col[u-1,b-u]=(-1)**u/sp.factorial(2*u)
        row=sp.diag(*[sp.Rational(2*(-1 if (r-c)%2 else 1),sp.factorial(2*r-1)) for r in range(1,b+1)])
        assert hh*col == row*mat
        # Highest moment coefficient is positive and has an exact Casoratian ratio.
        ee_prev=rr[b+1][0]*rr[b][1]-rr[b][0]*rr[b+1][1]
        if b <= 10:
            high=(4*b-1)*mat.inv()[0,b-1]
            asserted=4*b*(4*b-1)*ee_prev/(factors(c,b+2)[2]*ee)
            assert high == asserted and high > 0
        results['gap_four'].append(dict(b=b,p=p,q=q,determinant=str(determinant),positive_casoratian=str(ee)))
    # Generated fundamental rows: every minor with two increasing columns and
    # two increasing generated-row indices is negative, for any tested gap.
    for c in range(2,7):
        rr=fundamental(c,16)
        count=0
        for i in range(c+1,16):
            for s in range(i+1,17):
                for j in range(c):
                    for k in range(j+1,c):
                        assert rr[i][j]*rr[s][k]-rr[i][k]*rr[s][j] < 0
                        count+=1
        # Check kernel-ratio monotonicity independently on its finite domain.
        for s in range(c+1,16):
            ratios=[kernel(c,s+1,u)/kernel(c,s,u) for u in range(1,s)]
            assert all(ratios[u] > ratios[u+1] for u in range(len(ratios)-1))
        results['order_two_minors'].append(dict(gap=2*c,negative_minor_count=count))
    # Known sign obstruction: the full c=3 boundary array has no fixed sign.
    rr=fundamental(3,10)
    sign_examples=[]
    for b in [6,7]:
        dd=sp.Matrix(rr[b+1:b+4]).det()
        sign_examples.append(dict(b=b,c=3,determinant=str(dd),sign=int(sp.sign(dd))))
    assert sign_examples[0]['sign'] == -1 and sign_examples[1]['sign'] == 1
    results['higher_gap_sign_obstruction']=sign_examples
    results['ordinary_identity_4_8']=primitive_integer_rational_identity(4,8)
    results['finite_telescoping_certificates']=[finite_telescoping_certificate(p,q)
                                                for p,q in [(4,8),(8,12)]]
    results['status']='passed'
    (Path(output_path) if output_path else ROOT/'gap_four_exact_results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({"status":"passed","gap_four_pairs":len(results['gap_four']),
                      "negative_order_two_minors":sum(d['negative_minor_count'] for d in results['order_two_minors']),
                      "result_file":"gap_four_exact_results.json"},indent=2))

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=None)
    args = parser.parse_args()
    verify(args.output)
