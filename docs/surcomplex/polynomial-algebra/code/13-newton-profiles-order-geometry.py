#!/usr/bin/env python3
"""Exact finite checks accompanying Surcomplex Polynomial Algebra.

Run with Python 3 and SymPy. No network access, floating-point approximations,
or claims of proof-assistant verification are involved. The report is written
next to this script. Failed assertions produce a nonzero exit code.
"""
from __future__ import annotations

from pathlib import Path
import platform
import random
import sys
import time
import traceback

import sympy as s

T = s.Symbol('t', real=True, positive=True)
Z, X, Y, L = s.symbols('z X Y L')
REPORT = Path(__file__).resolve().with_name('verification_report.txt')
LOG: list[str] = []
COUNT = 0


def note(text: str) -> None:
    LOG.append(text)
    print(text, flush=True)


def check(name: str, condition: object) -> None:
    global COUNT
    if not bool(condition):
        raise AssertionError(name)
    COUNT += 1
    LOG.append(f'PASS {COUNT:03d}: {name}')


def equal(a: object, b: object) -> bool:
    if isinstance(a, s.MatrixBase) or isinstance(b, s.MatrixBase):
        delta = s.Matrix(a) - s.Matrix(b)
        return all(s.cancel(q) == 0 for q in delta)
    return s.cancel(s.sympify(a) - s.sympify(b)) == 0


def valuation(expr: object) -> s.Expr:
    """Exact t-adic valuation of a rational function over an exact field."""
    expr = s.cancel(s.sympify(expr))
    if expr == 0:
        return s.oo
    numerator, denominator = s.fraction(expr)
    def order(poly: s.Expr) -> int:
        return min(m[0] for m, c in s.Poly(poly, T).terms() if c != 0)
    return s.Integer(order(numerator) - order(denominator))


def coefficient_precision(expr: object, variable: s.Symbol = Z) -> s.Expr:
    poly = s.Poly(s.expand(expr), variable)
    return min((valuation(c) for c in poly.all_coeffs()), default=s.oo)


def initial(poly: s.Expr, center: s.Expr, rho: int) -> tuple[s.Expr, s.Expr]:
    transformed = s.Poly(s.expand(poly.subs(Z, center + T**rho * X)), X)
    weight = min(valuation(c) for c in transformed.all_coeffs())
    result = 0
    for (j,), coefficient in transformed.terms():
        normalized = s.cancel(coefficient * T**(-weight))
        result += normalized.subs(T, 0) * X**j
    return weight, s.expand(result)


def multiplication_matrix(poly: s.Expr, h: s.Expr, variable: s.Symbol = Z) -> s.Matrix:
    n = s.degree(poly, variable)
    cols = []
    for j in range(n):
        remainder = s.Poly(s.rem(h * variable**j, poly, variable), variable)
        cols.append(s.Matrix([remainder.nth(i) for i in range(n)]))
    return s.Matrix.hstack(*cols)


def hensel_lift(reference: list[s.Expr], error: s.Expr, order: int) -> list[s.Expr]:
    """Finite integer-power truncation of the article's coprime-factor recursion."""
    degree = [s.degree(p, Z) for p in reference]
    total = sum(degree)
    columns = []
    for i, d in enumerate(degree):
        others = s.prod(p for j, p in enumerate(reference) if j != i)
        for k in range(d):
            col = s.Poly(s.expand(others * Z**k), Z)
            columns.append(s.Matrix([col.nth(j) for j in range(total)]))
    inverse = s.Matrix.hstack(*columns).inv()
    target = s.expand(s.prod(reference) + error)
    factors = list(reference)
    for nu in range(1, order + 1):
        residual = s.Poly(s.expand(target - s.prod(factors)), T).nth(nu)
        residual = s.Poly(residual, Z)
        correction = inverse * s.Matrix([residual.nth(j) for j in range(total)])
        offset = 0
        for i, d in enumerate(degree):
            factors[i] = s.expand(factors[i] + T**nu * sum(
                correction[offset + j] * Z**j for j in range(d)))
            offset += d
    return factors


def checks_newton_and_clusters() -> None:
    note('\n1. Newton profiles, leading roots, and nested critical directions')
    p = Z**3 - T**2 * Z - T**5
    check('cubic initial polynomial at rho=1', initial(p, 0, 1) == (3, X**3 - X))
    check('cubic initial polynomial at rho=3', initial(p, 0, 3) == (5, -X - 1))
    for rho in range(-2, 7):
        weight, ip = initial(p, 0, rho)
        check(f'cubic profile at integer rho={rho}', weight == min(5, 2 + rho, 3 * rho))
        p_ip = s.Poly(ip, X)
        open_count = min(m[0] for m, c in p_ip.terms() if c != 0)
        check(f'cubic ball count at integer rho={rho}',
              s.degree(ip, X) == sum(r >= rho for r in (1, 1, 3))
              and open_count == sum(r > rho for r in (1, 1, 3)))
    approx = [T + T**3 / 2 - 3 * T**5 / 8,
              -T + T**3 / 2 + 3 * T**5 / 8, -T**3 - T**7]
    for j, (a, bound) in enumerate(zip(approx, (9, 9, 13)), 1):
        check(f'cubic approximate root {j}: residual valuation >= {bound}',
              valuation(p.subs(Z, a)) >= bound)

    quartic = s.expand(Z * (Z - T**3) * (Z - T) * (Z - 1))
    derivative = 4 * Z**3 - 3 * (1 + T + T**3) * Z**2 + 2 * (T + T**3 + T**4) * Z - T**4
    check('nested quartic derivative', equal(s.diff(quartic, Z), derivative))
    for rho, weight, ip in [(0, 0, X**3 * (X - 1)),
                            (1, 3, -X**2 * (X - 1)),
                            (3, 7, X * (X - 1))]:
        got_weight, got_ip = initial(quartic, 0, rho)
        check(f'nested quartic initial polynomial, rho={rho}',
              got_weight == weight and equal(got_ip, ip))
        dw, dip = initial(derivative, 0, rho)
        check(f'nested quartic derivative initial polynomial, rho={rho}',
              dw == weight - rho and equal(dip, s.diff(ip, X)))
    check('three residual critical directions',
          s.diff(X**3 * (X - 1), X).subs(X, s.Rational(3, 4)) == 0
          and s.diff(-X**2 * (X - 1), X).subs(X, s.Rational(2, 3)) == 0
          and s.diff(X * (X - 1), X).subs(X, s.Rational(1, 2)) == 0)


def checks_lifting_and_precision() -> None:
    note('\n2. Coprime lifting, sharp collision, and separated-root precision')
    p = Z**2 + T * Z - 1 + T**2
    root_plus = 1 - T/2 - 3*T**2/8 - 9*T**4/128
    root_minus = -1 - T/2 + 3*T**2/8 + 9*T**4/128
    for name, root in [('plus', root_plus), ('minus', root_minus)]:
        check(f'quadratic factor example, {name} root through degree four', valuation(p.subs(Z, root)) >= 6)
    check('quadratic approximate factors agree modulo t^6',
          coefficient_precision(p - (Z-root_plus)*(Z-root_minus)) >= 6)

    examples = [([Z**2, Z-1], T*(Z**2+2*Z+3) + T**2*(Z+1) + T**3, 5),
                ([Z, Z-1, Z+2], T*Z**2 + T**2*(Z+1), 5)]
    for j, (reference, error, order) in enumerate(examples, 1):
        factors = hensel_lift(reference, error, order)
        check(f'Hensel recursion {j}: product correct through t^{order}',
              coefficient_precision(s.prod(reference)+error-s.prod(factors)) >= order+1)
        check(f'Hensel recursion {j}: normalized degrees and reductions',
              all(s.degree(a, Z) == s.degree(b, Z) and equal(a.subs(T, 0), b)
                  for a, b in zip(factors, reference)))

    for a in range(1, 6):
        p = Z*(Z-T**a)
        q = p + T**(2*a)/4
        check(f'sharp collision at separation t^{a}', equal(q, (Z-T**a/2)**2))
        check(f'quadratic discriminant valuation, a={a}', valuation(s.discriminant(p, Z)) == 2*a)
        check(f'double-root gcd, a={a}', s.degree(s.gcd(q, s.diff(q, Z)), Z) == 1)

    roots = [s.Integer(0), T**3, T, s.Integer(1)]
    p = s.expand(s.prod(Z-r for r in roots))
    dp = s.diff(p, Z)
    di = [valuation(dp.subs(Z, r)) for r in roots]
    delta = [max(valuation(r-q) for j, q in enumerate(roots) if j != i)
             for i, r in enumerate(roots)]
    check('nested quartic derivative valuations (4,4,2,0)', di == [4, 4, 2, 0])
    check('nested quartic maximal separation valuations (3,3,1,0)', delta == [3, 3, 1, 0])
    check('nested quartic threshold 7 and discriminant valuation 10',
          max(d+h for d,h in zip(di, delta)) == 7 and valuation(s.discriminant(p, Z)) == 10)
    error = T**8*(1+Z)
    q = p + error
    leading = [T**4, T**3-T**4, T+T**6, 1-2*T**8]
    for i, (root, candidate) in enumerate(zip(roots, leading)):
        check(f'nested quartic leading perturbed root {i+1}: residual valuation >=9',
              valuation(q.subs(Z, candidate)) >= 9)
        check(f'nested quartic root {i+1}: leading displacement valuation {8-di[i]}',
              valuation(candidate-root) == 8-di[i])
        newton = s.cancel(root-error.subs(Z, root)/dp.subs(Z, root))
        bound = 16-di[i]-delta[i]
        check(f'nested quartic Newton point {i+1}: residual valuation >= {bound}',
              valuation(q.subs(Z, newton)) >= bound)
    for rho in (0, 1, 3):
        check(f'perturbed quartic initial polynomial preserved at rho={rho}',
              initial(q, 0, rho) == initial(p, 0, rho))
        check(f'perturbed quartic critical directions preserved at rho={rho}',
              initial(s.diff(q, Z), 0, rho) == initial(dp, 0, rho))


def checks_order_geometry() -> None:
    note('\n3. Jensen identity and finite-dimensional compression')
    x, y, a, b = s.symbols('x y a b', real=True)
    dm = (x-a)**2+(y-b)**2
    dp = (x-a)**2+(y+b)**2
    lhs = -((y-b)/dm+(y+b)/dp)/y
    rhs = -2*((x-a)**2+y**2-b**2)/(dm*dp)
    check('Jensen conjugate-pair rational identity', equal(lhs, rhs))

    root_sets = [[s.Integer(0), s.Integer(2)],
                 [s.Integer(0), 1+s.I, s.Integer(-2)],
                 [s.Integer(0), T, 1+s.I*T, T**2-s.I]]
    for roots in root_sets:
        n = len(roots)
        u = s.zeros(n, n-1)
        for k in range(1, n):
            denominator = s.sqrt(k*(k+1))
            for row in range(k):
                u[row, k-1] = 1/denominator
            u[k, k-1] = -k/denominator
        e = s.ones(n, 1)/s.sqrt(n)
        check(f'Helmert orthonormality for n={n}', equal(u.T*u, s.eye(n-1)) and equal(u.T*e, s.zeros(n-1,1)))
        d = s.diag(*roots)
        matrix = u.T*d*u
        p = s.expand(s.prod(Z-r for r in roots))
        check(f'compression characteristic polynomial P\'/n, n={n}',
              equal(matrix.charpoly(Z).as_expr(), s.diff(p, Z)/n))
        norm_sum = sum(r*s.conjugate(r) for r in roots)
        centroid_sum = sum(roots)
        expected = s.Rational(n-2,n)*norm_sum + centroid_sum*s.conjugate(centroid_sum)/n**2
        check(f'compression squared-norm identity, n={n}',
              equal(s.trace(matrix*matrix.conjugate().T), expected))

    n = 4
    def centered_commutator(roots: list[s.Expr]) -> s.Matrix:
        projection = s.eye(n)-s.ones(n,n)/n
        d = s.diag(*roots)
        m = projection*d*projection
        return s.simplify(m*m.conjugate().T-m.conjugate().T*m)
    collinear = [1+s.I+(2-s.I)*r for r in (-2,0,3,7)]
    check('normal compression in a collinear example', equal(centered_commutator(collinear), s.zeros(4)))
    check('nonnormal compression for four noncollinear roots',
          not equal(centered_commutator([1,s.I,-1,-s.I]), s.zeros(4)))


def checks_residue_and_resultants() -> None:
    note('\n4. Residue duality, trace, discriminant, and resultants')
    a, b = s.symbols('a b')
    p = Z**3-a*Z-b
    def lam(h: s.Expr) -> s.Expr:
        return s.Poly(s.rem(h, p, Z), Z).nth(2)
    gram = s.Matrix(3,3,lambda i,j: lam(Z**(i+j)))
    expected = s.Matrix([[0,0,1],[0,1,0],[1,0,a]])
    check('cubic residue Gram matrix and determinant', equal(gram, expected) and gram.det() == -1)
    dual = [Z**2-a,Z,s.Integer(1)]
    check('cubic residue-dual basis', all(equal(lam(Z**i*dual[j]), int(i==j)) for i in range(3) for j in range(3)))
    check('cubic trace element equals P\'', equal(sum(Z**i*dual[i] for i in range(3)), s.diff(p,Z)))
    trace_gram = s.Matrix(3,3,lambda i,j: s.trace(multiplication_matrix(p,Z**(i+j))))
    expected_trace = s.Matrix([[3,0,2*a],[0,2*a,3*b],[2*a,3*b,2*a**2]])
    check('cubic trace Gram matrix', equal(trace_gram, expected_trace))
    check('cubic trace determinant is discriminant', equal(trace_gram.det(),4*a**3-27*b**2))

    collision = (Z-2*T)*(Z+T)**2
    partial = 1/(9*T**2*(Z-2*T))-1/(9*T**2*(Z+T))-1/(3*T*(Z+T)**2)
    check('collision partial-fraction identity', equal(1/collision,partial))
    for k in range(7):
        h = Z**k
        actual = s.Poly(s.rem(h,collision,Z),Z).nth(2)
        formula = (h.subs(Z,2*T)-h.subs(Z,-T))/(9*T**2)-s.diff(h,Z).subs(Z,-T)/(3*T)
        check(f'collision residue formula on z^{k}', equal(actual,formula))
        check(f'collision trace formula on z^{k}',
              equal(s.trace(multiplication_matrix(collision,h)),h.subs(Z,2*T)+2*h.subs(Z,-T)))

    for n in range(1,7):
        pp = Z+1 if n==1 else Z**n-Z-1
        gg = s.Matrix(n,n,lambda i,j: s.Poly(s.rem(Z**(i+j),pp,Z),Z).nth(n-1))
        check(f'residue Gram determinant, degree {n}', gg.det() == (-1)**(n*(n-1)//2))
        tt = s.Matrix(n,n,lambda i,j: s.trace(multiplication_matrix(pp,Z**(i+j))))
        check(f'trace Gram determinant, degree {n}', equal(tt.det(),s.discriminant(pp,Z)))
    pp = Z**3-T*Z-T**2
    qq = Z**2+T*Z+1
    check('resultant equals determinant of multiplication',
          equal(s.resultant(pp,qq,Z),multiplication_matrix(pp,qq).det()))


def checks_coupled_system() -> None:
    note('\n5. Coupled two-variable finite algebra')
    x, y = s.symbols('x y')
    wx = s.Matrix([[0,T**2,0,0],[1,0,0,T**2],[0,T,0,T**2],[0,0,1,0]])
    wy = s.Matrix([[0,0,0,T**3],[0,0,T,0],[1,0,0,T**2],[0,1,0,0]])
    check('coupled multiplication matrices commute',equal(wx*wy,wy*wx))
    check('coupled relation Wx^2=t Wy+t^2 I',equal(wx**2,T*wy+T**2*s.eye(4)))
    check('coupled relation Wy^2=t Wx',equal(wy**2,T*wx))
    check('characteristic polynomial of Wy',equal(wy.charpoly(L).as_expr(),L**4-T**3*L-T**4))
    check('characteristic polynomial of Wx',equal(wx.charpoly(L).as_expr(),L**4-2*T**2*L**2-T**3*L+T**4))
    f1=x**2-T*y-T**2
    f2=y**2-T*x
    check('coupled elimination resultant',equal(s.resultant(f1,f2,x),y**4-T**3*y-T**4))
    p=Y**4-Y-1
    check('ordinary quartic is squarefree',s.gcd(p,s.diff(p,Y))==1)
    check('coupled parametrization satisfies first equation modulo quartic',
          s.rem(s.expand(f1.subs({x:T*Y**2,y:T*Y})),p,Y)==0)
    check('coupled parametrization satisfies second equation',equal(f2.subs({x:T*Y**2,y:T*Y}),0))
    jac=s.det(s.Matrix([[s.diff(f1,x),s.diff(f1,y)],[s.diff(f2,x),s.diff(f2,y)]]))
    check('coupled Jacobian normalization',equal(jac.subs({x:T*Y**2,y:T*Y}),T**2*(4*Y**3-1)))


def checks_matching() -> None:
    note('\n6. Finite matching tests: exact rational-power examples')
    rng=random.Random(20260921)
    base=[s.Integer(0),s.Integer(1),s.Integer(-1),T,-T,T**2,T+T**3]
    for case in range(20):
        n=2+case%5
        denominator=(1,2,3,5)[case%4]
        roots=[rng.choice(base) for _ in range(n)]
        exponent=rng.randrange(2,8)
        other=[r+rng.choice([-2,-1,1,2])*T**(exponent+rng.randrange(3)) for r in roots]
        rng.shuffle(other)
        p=s.Poly(s.prod(Z-r for r in roots),Z).as_expr().expand()
        q=s.Poly(s.prod(Z-r for r in other),Z).as_expr().expand()
        eps=coefficient_precision(q-p)
        check(f'matching case {case+1}: positive coefficient precision',eps!=s.oo and eps>0)
        all_roots=roots+other
        threshold=eps/n
        parent=list(range(2*n))
        def find(i: int) -> int:
            while parent[i]!=i:
                parent[i]=parent[parent[i]]
                i=parent[i]
            return i
        for i in range(2*n):
            for j in range(i):
                if valuation(all_roots[i]-all_roots[j])>=threshold:
                    parent[find(i)]=find(j)
        clusters: dict[int,tuple[list[int],list[int]]]={}
        for i in range(2*n):
            bucket=clusters.setdefault(find(i),([],[]))
            bucket[int(i>=n)].append(i)
        balanced=all(len(a)==len(b) for a,b in clusters.values())
        check(f'matching case {case+1}: balanced multiplicities in every precision ball',balanced)
        matched=[(i,j) for a,b in clusters.values() for i,j in zip(a,b)]
        check(f'matching case {case+1}: a complete bijection at epsilon/n',
              len(matched)==n and all(valuation(all_roots[i]-all_roots[j])>=threshold for i,j in matched))
        # Interpret the algebraic uniformizer T as t^(1/denominator), so all
        # valuations, including epsilon and epsilon/n, are divided by that D.
        LOG.append(f'  Case {case+1}: n={n}, uniformizer=t^(1/{denominator}), '
                   f'epsilon={eps/denominator}, matching threshold={threshold/denominator}, '
                   f'clusters={len(clusters)}.')


def main() -> int:
    start=time.monotonic()
    note('SURCOMPLEX POLYNOMIAL ALGEBRA — EXACT FINITE VERIFICATION')
    note(f'Python {platform.python_version()}; SymPy {s.__version__}')
    note('Arithmetic: exact integers, rationals, algebraic constants, rational functions, and finite formal truncations.')
    try:
        checks_newton_and_clusters()
        checks_lifting_and_precision()
        checks_order_geometry()
        checks_residue_and_resultants()
        checks_coupled_system()
        checks_matching()
    except Exception:
        LOG.append('\nFAILED\n'+traceback.format_exc())
        REPORT.write_text('\n'.join(LOG)+'\n',encoding='utf-8')
        traceback.print_exc()
        return 1
    note(f'\nSUCCESS: {COUNT} exact checks passed.')
    note(f'Elapsed execution: {time.monotonic()-start:.2f} seconds.')
    note('Scope: 20 generated matching cases, degrees 2–6, seed 20260921; exponent denominators 1,2,3,5. '
         'Finite Hensel recursions are checked through t^5; root and residue truncation ranges appear above.')
    note('LIMITATION: These tests do not formally verify the general mathematical theorems, arbitrary Hahn supports, '
         'transfinite recursion, or real-closed-field transfer. The article supplies the proofs.')
    REPORT.write_text('\n'.join(LOG)+'\n',encoding='utf-8')
    return 0


if __name__=='__main__':
    sys.exit(main())
