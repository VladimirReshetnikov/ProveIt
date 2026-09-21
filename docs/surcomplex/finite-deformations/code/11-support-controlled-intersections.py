#!/usr/bin/env python3
"""Exact symbolic consistency checks for surcomplex_intersections.tex.

Requires Python 3.9+ and SymPy.  This checks finite algebraic identities and
specified truncations; it is not a formal proof of the Hahn-support theorems.
Run: python verify_examples.py
"""
from __future__ import annotations
from itertools import combinations
from pathlib import Path
import sys
import sympy as s

x, y, z, tau, a, T = s.symbols('x y z tau a T')
CHECKS: list[str] = []

def check(label: str, expression) -> None:
    if isinstance(expression, s.MatrixBase):
        ok = all(s.expand(v) == 0 for v in expression)
    elif isinstance(expression, bool):
        ok = expression
    else:
        ok = s.simplify(s.expand(expression)) == 0
    if not ok:
        raise AssertionError(f'{label}: {expression}')
    CHECKS.append(label)

def trunc(f, order: int):
    return s.Add(*(c * tau**m[0] for m, c in s.Poly(s.expand(f), tau).terms()
                   if m[0] < order))

def rem(f, var, degree: int):
    return s.Add(*(c * var**m[0] for m, c in s.Poly(s.expand(f), var).terms()
                   if m[0] < degree))

def div(f, var, degree: int):
    return s.expand((f - rem(f, var, degree)) / var**degree)

def clean(form):
    return {I: s.expand(c) for I, c in form.items() if s.expand(c) != 0}

def plus(*forms):
    out = {}
    for f in forms:
        for I, c in f.items():
            out[I] = out.get(I, 0) + c
    return clean(out)

def neg(form):
    return {I: -c for I, c in form.items()}

def differential(form, fs):
    out = {}
    for I, c in form.items():
        for p, j in enumerate(I):
            J = I[:p] + I[p+1:]
            out[J] = out.get(J, 0) + (-1)**p * fs[j] * c
    return clean(out)

def homotopy(form, variables, degrees):
    out = {}
    for I, c in form.items():
        for j, (v, d) in enumerate(zip(variables, degrees)):
            if j in I or any(i < j for i in I):
                continue
            g = c
            for i in range(j):
                g = rem(g, variables[i], degrees[i])
            g = div(g, v, d)
            J = tuple(sorted((j,) + I))
            sign = (-1)**sum(i < j for i in I)
            out[J] = out.get(J, 0) + sign * g
    return clean(out)

def projection(form, variables, degrees):
    g = form.get((), 0)
    for v, d in zip(variables, degrees):
        g = rem(g, v, d)
    return clean({(): g})

def form_check(label, form):
    check(label, not clean(form))

def test_contraction():
    variables, degrees = (x, y, z), (2, 3, 2)
    f0 = (x**2, y**3, z**2)
    errors = (tau * (1+y*z), tau**2 * (x+z), tau * (x*y+1))
    fs = tuple(g+e for g,e in zip(f0,errors))
    h = lambda c: homotopy(c, variables, degrees)
    d0 = lambda c: differential(c, f0)
    d = lambda c: differential(c, fs)
    delta = lambda c: differential(c, errors)
    Q = lambda c: plus(c, delta(h(c)))
    poly = 1+x**4*y**3+2*x*y**5*z**3+z**4
    for q in range(4):
        for I in combinations(range(3), q):
            c = {I: poly}
            suffix = str(I)
            form_check('Koszul contraction '+suffix,
                       plus(d0(h(c)), h(d0(c)), neg(c),
                            projection(c, variables, degrees)))
            form_check('h squared '+suffix, h(h(c)))
            form_check('Perturbation conjugation '+suffix,
                       plus(d(Q(c)), neg(Q(d0(c)))))

def test_finite_division():
    order = 6
    variables, degrees = (x, y), (2, 2)
    errors = (tau*(1+y)+tau**2*x*y, tau*x+tau**2*x*x)
    fs = (x*x+errors[0], y*y+errors[1])
    def h0(f):
        return (div(f,x,2), div(rem(f,x,2),y,2))
    def L(f):
        return trunc(sum(e*g for e,g in zip(errors,h0(f))),order)
    def division(f):
        term, S = trunc(f,order), s.Integer(0)
        for _ in range(order):
            S += term
            term = -L(term)
        S = trunc(S,order)
        nf = rem(rem(S,x,2),y,2)
        return s.expand(nf), h0(S)
    f = x**5+y**4+x*y+tau*(x**3*y+7)
    nf, quotients = division(f)
    check('Division certificate modulo tau^6',
          trunc(f-nf-sum(F*g for F,g in zip(fs,quotients)),order))
    box = (1,x,y,x*y)
    for i,F in enumerate(fs):
        for j,b in enumerate(box):
            check(f'Ideal annihilation F{i+1} basis{j}',division(F*b)[0])
    def col(f):
        p = s.Poly(division(f)[0],x,y)
        return s.Matrix([p.coeff_monomial(b) for b in box])
    X = s.Matrix.hstack(*(col(x*b) for b in box))
    Y = s.Matrix.hstack(*(col(y*b) for b in box))
    check('Coupled multiplication matrices commute modulo tau^6',
          (X*Y-Y*X).applyfunc(lambda e: trunc(e,order)))

def test_four_point_example():
    # Ordered basis (1,x,y,xy), with x^2=tau*y, y^2=tau*a*x.
    X = s.Matrix([[0,0,0,0],[1,0,0,tau**2*a],
                  [0,tau,0,0],[0,0,1,0]])
    Y = s.Matrix([[0,0,0,0],[0,0,tau*a,0],
                  [1,0,0,tau**2*a],[0,1,0,0]])
    I = s.eye(4)
    J = 4*X*Y-tau**2*a*I
    check('Example commutation',X*Y-Y*X)
    check('Example first equation',X*X-tau*Y)
    check('Example second equation',Y*Y-tau*a*X)
    check('Characteristic polynomial of x',X.charpoly(T).as_expr()-(T**4-tau**3*a*T))
    check('Jacobian discriminant',J.det()+27*tau**8*a**4)
    check('Trace of Jacobian',s.trace(J)-8*tau**2*a)
    # The residue of a normal form is its xy coefficient in this example.
    residue = s.Matrix([[0,0,0,1]])
    basis_matrices = (I,X,Y,X*Y)
    gram = s.Matrix([[(residue*B*C*s.Matrix([1,0,0,0]))[0]
                       for C in basis_matrices] for B in basis_matrices])
    check('Perfect residue pairing example',gram.det()-1)
    for index,B in enumerate(basis_matrices):
        check(f'Trace-residue formula basis {index}',
              s.trace(B)-(residue*B*J*s.Matrix([1,0,0,0]))[0])
    # Direct geometric torus expansion and the sum over moving simple roots.
    for degree in range(13):
        coeff = s.Integer(0)
        for k in range(degree+1):
            l = degree-k
            p,q = 2*k+1-l,2*l+1-k
            if min(p,q)>=0:
                coeff += 1/(s.factorial(p)*s.factorial(q))
        exact = (s.Integer(2)**(degree+2)+2*(-1)**(degree+2))/(3*s.factorial(degree+2))
        check(f'Exponential residue coefficient tau^{degree}',coeff-exact)
    return X,Y,gram

def main() -> None:
    test_contraction()
    test_finite_division()
    X,Y,gram = test_four_point_example()
    text = '\n'.join([
        'SURCOMPLEX FINITE-INTERSECTION SYMBOLIC CHECKS',
        f'Python {sys.version.split()[0]}; SymPy {s.__version__}',
        f'{len(CHECKS)} checks passed.', '',
        *('PASS: '+label for label in CHECKS), '',
        'Exact example matrices (basis 1,x,y,xy):',
        'X = '+str(X),'Y = '+str(Y),'Residue Gram matrix = '+str(gram), '',
        'Finite division calculations are modulo tau^6.',
        'Exponential residue coefficients checked through tau^12.',
        'These are consistency checks, not machine-checked proofs of the article.',
        'The general well-ordered-support and multiplicity arguments are in the PDF.',
        ''
    ])
    Path(__file__).with_name('verification_report.txt').write_text(text,encoding='utf-8')
    print(text)

if __name__ == '__main__':
    main()
