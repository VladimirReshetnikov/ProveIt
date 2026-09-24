#!/usr/bin/env python3
"""Exact symbolic checks for the accompanying surcomplex research article.

Requires Python 3 and SymPy. No numerical approximation to a surreal number is
used. The indeterminates t and s remain algebraically independent; substituting
s = omega**(-Omega) is justified by the support proofs in the article.
These checks are not formal verification of the general theorems.
"""
from __future__ import annotations
import itertools
from pathlib import Path
try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required: install sympy and rerun this script.") from exc

lines: list[str] = []

def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    lines.append("PASS: " + name)


def zero(expr: sp.Expr) -> bool:
    return sp.simplify(sp.expand(expr)) == 0


def main() -> None:
    t, s, a, X, x, y, q = sp.symbols('t s a X x y q')
    I = sp.eye(4)
    Mx = sp.Matrix([[0,a,0,t*a],[1,0,0,t**2],[0,t,0,a],[0,0,1,0]])
    My = sp.Matrix([[0,0,a,t*a],[0,0,t,a],[1,0,0,t**2],[0,1,0,0]])
    Z = sp.zeros(4)
    check('multiplication matrices commute', (Mx*My-My*Mx).applyfunc(sp.expand) == Z)
    check('first defining relation on matrices', (Mx**2-t*My-a*I).applyfunc(sp.expand) == Z)
    check('second defining relation on matrices', (My**2-t*Mx-a*I).applyfunc(sp.expand) == Z)
    expected = X**4-2*a*X**2-t**3*X+a**2-a*t**2
    check('characteristic polynomial', zero(Mx.charpoly(X).as_expr()-expected))
    check('characteristic factorization', zero(expected-(X**2-t*X-a)*(X**2+t*X+t**2-a)))
    check('trace x and trace y', sp.trace(Mx)==0 and sp.trace(My)==0)
    check('trace x squared', zero(sp.trace(Mx**2)-4*a))
    check('trace xy', zero(sp.trace(Mx*My)-3*t**2))

    aval = sp.Rational(3,4)*t**2+s
    # Check root formulas by polynomial reduction, rather than numerical radicals.
    r = sp.symbols('r')
    diagx = t/2+r
    diag_relation = r**2-t**2-s
    for sign in [1,-1]:
        dx = t/2+sign*r
        expression = dx**2-t*dx-aval
        check(f'diagonal root formula, sign {sign}', sp.rem(sp.expand(expression),diag_relation,r)==0)
        ox, oy = -t/2+sign*r, -t/2-sign*r
        check(f'off-diagonal first equation, sign {sign}', sp.rem(sp.expand(ox**2-t*oy-aval),r**2-s,r)==0)
        check(f'off-diagonal second equation, sign {sign}', sp.rem(sp.expand(oy**2-t*ox-aval),r**2-s,r)==0)
        check(f'off-diagonal Jacobian, sign {sign}', zero(4*ox*oy-t**2+4*r**2))

    binomial = 1+q/2-q**2/8+q**3/16-5*q**4/128+7*q**5/256
    check('square-root expansion through degree five', sp.series(binomial**2-(1+q),q,0,6).removeO()==0)
    Jminus = sp.series(4*(sp.Rational(1,2)-sp.sqrt(1+q))**2-1,q,0,4).removeO()
    check('Jacobian at the near diagonal root', zero(Jminus-(2*q+q**2/2-q**3/4)))

    # At s=0 the eliminated quartic has a triple root and a simple root.
    check('triple collision at s=0', zero(expected.subs(a,sp.Rational(3,4)*t**2)-(X-sp.Rational(3,2)*t)*(X+t/2)**3))

    # In this quadratic example the torus residue is the xy coefficient
    # of the box normal form. Test its Frobenius and trace identities.
    basis_mats = [I,Mx,My,Mx*My]
    v0 = sp.Matrix([1,0,0,0])
    residue = lambda M: (M*v0)[3]
    G = sp.Matrix(4,4,lambda i,j: sp.expand(residue(basis_mats[i]*basis_mats[j])))
    Gexpected = sp.Matrix([[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,t**2]])
    check('residue Gram matrix', G == Gexpected)
    check('residue Gram determinant', sp.det(G)==1)
    Ginv = G.inv()
    dual_mats = [sum((Ginv[k,j]*basis_mats[k] for k in range(4)),sp.zeros(4)) for j in range(4)]
    Euler = sum((basis_mats[j]*dual_mats[j] for j in range(4)),sp.zeros(4))
    check('Euler element is Jacobian in this example', (Euler-(4*Mx*My-t**2*I)).applyfunc(sp.expand)==Z)
    for j,M in enumerate(basis_mats):
        check(f'trace-residue identity on basis element {j}', zero(residue(Euler*M)-sp.trace(M)))

    # Explicit simple-root Jacobian weights, algebraically reduced with r^2=t^2+s.
    diag_plus,diag_minus=t/2+r,t/2-r
    Jp,Jm=4*diag_plus**2-t**2,4*diag_minus**2-t**2
    numerator = sp.together(1/Jp+1/Jm-1/(2*s)).as_numer_denom()[0]
    check('cancellation of three large residue weights: constant numerator', sp.rem(sp.expand(numerator),r**2-t**2-s,r)==0)
    numerator = sp.together(diag_plus**2/Jp+diag_minus**2/Jm-(t**2/4-s)/(2*s)-1).as_numer_denom()[0]
    check('Jacobian-weighted xy sum equals one', sp.rem(sp.expand(numerator),r**2-t**2-s,r)==0)

    # Verify the explicit two-variable Koszul contraction on monomial samples.
    def P(f: sp.Expr, var: sp.Symbol, d: int=2) -> sp.Expr:
        terms = sp.Poly(sp.expand(f), var).as_dict()
        return sp.expand(sum((coef * var**power[0]
                              for power, coef in terms.items() if power[0] < d),
                             sp.S.Zero))
    def Q(f: sp.Expr, var: sp.Symbol, d: int=2) -> sp.Expr:
        return sp.cancel((f-P(f,var,d))/var**d)
    def h0(f: sp.Expr) -> tuple[sp.Expr,sp.Expr]:
        return Q(f,x),P(Q(f,y),x)
    sample_count=0
    for ix,iy in itertools.product(range(7),repeat=2):
        f=x**ix*y**iy
        h1,h2=h0(f)
        check_expr=sp.expand(x**2*h1+y**2*h2-(f-P(P(f,x),y)))
        if check_expr != 0:
            raise AssertionError('degree-zero contraction')
        # e1 and e2 independently: d h + h d = identity in degree one.
        for A,B in [(f,sp.S.Zero),(sp.S.Zero,f)]:
            top=Q(B,x)
            hdA,hdB=h0(x**2*A+y**2*B)
            if not zero(-y**2*top+hdA-A) or not zero(x**2*top+hdB-B):
                raise AssertionError('degree-one contraction')
        if not zero(Q(x**2*f,x)-f):
            raise AssertionError('degree-two contraction')
        sample_count+=1
    check(f'Koszul contraction in all degrees on {sample_count} monomials',True)

    lines.extend(['', 'Characteristic polynomial:', str(sp.factor(expected)),
                  '', 'Residue Gram matrix:', str(G),
                  '', f'SymPy version: {sp.__version__}',
                  'All algebraic checks use exact symbolic arithmetic.',
                  'No claim of machine-checked proofs of the general theorems.'])
    text='\n'.join(lines)+'\n'
    print(text,end='')
    Path(__file__).with_name('verification_report.txt').write_text(text,encoding='utf-8')

if __name__=='__main__':
    main()
