#!/usr/bin/env python3
"""Exact companion checks for All-Degree Rigidity of a Weighted Keller Class.

Run: python verify_results.py --output verification.json
Requires Python 3.10+ and SymPy (tested with 1.14.0).

This checks finite polynomial identities and rational linear algebra. It is not
an exhaustive search and does not replace the article's all-degree argument.
No network, floating-point arithmetic, or external CAS service is used.
"""
from __future__ import annotations
import argparse
import json
import platform
from pathlib import Path
from typing import Any
import sympy as S


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def zero(expr: S.Expr, message: str) -> None:
    require(S.cancel(S.expand(expr)) == 0, message)


def same(left: S.Matrix, right: S.Matrix, message: str) -> None:
    require(left.shape == right.shape, message + ': shape mismatch')
    for i, entry in enumerate(left - right):
        zero(entry, message + f': entry {i}')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('verification.json'))
    args = parser.parse_args()
    checks: list[str] = []
    def passed(name: str) -> None:
        checks.append(name)
        print('PASS:', name, flush=True)

    t, v, x, y, z, a, b = S.symbols('t v x y z a b')
    variables = S.Matrix([x, y, z])
    rat = S.Rational
    def det_reduced(p: S.Expr, q: S.Expr, r: S.Expr) -> S.Expr:
        return S.expand(S.det(S.Matrix([
            [-2*p, S.diff(p,t), S.diff(p,v)],
            [-q, S.diff(q,t), S.diff(q,v)],
            [r, S.diff(r,t), S.diff(r,v)]
        ])))
    def lift(p: S.Expr, q: S.Expr, r: S.Expr) -> S.Matrix:
        sub = {t:x*y, v:x*x*z}
        return S.Matrix([S.cancel(p.subs(sub)/x**2),
                         S.cancel(q.subs(sub)/x), S.expand(x*r.subs(sub))])

    p = (v-rat(8,9)*a*t**2-2*a*b*t*v+rat(28,27)*a**2*b*t**3
         +rat(4,3)*a**2*b**2*t**2*v-rat(8,27)*a**3*b**2*t**4
         -rat(8,27)*a**3*b**3*t**3*v)
    q = t+9*b*v-8*a*b*t**2-12*a*b**2*t*v+4*a**2*b**2*t**3+4*a**2*b**3*t**2*v
    r = 1+a*b*t+a*b**2*v
    zero(det_reduced(p,q,r)+1, 'family reduced determinant')
    F = lift(p,q,r)
    zero(F.jacobian(variables).det()+1, 'family full determinant')
    passed('two-parameter family: both Jacobian determinant computations equal -1')

    base = F.subs({a:1,b:1})
    u0 = 1+x*y
    h0 = u0**2*z+y**2*(1+3*u0)
    original = S.Matrix([u0*h0,y+3*x*h0,x*(5-3*u0-x*x*z)])
    transformed = S.diag(-rat(1,2),-rat(3,2),rat(1,2))*original.subs(
        {x:x,y:-rat(2,3)*y,z:-2*z}, simultaneous=True)
    same(base, transformed, 'normalization of original map')
    zero(original.jacobian(variables).det()+2, 'original determinant')
    same(original.subs({x:-1,y:1,z:5}),
         original.subs({x:0,y:-2,z:-16}), 'original integral collision')
    passed('normalization agrees with the repository map; original collision verified')

    diagonal = S.diag(1/(a*b**2),1/(a*b),1)*base.subs(
        {x:x,y:a*b*y,z:a*b**2*z}, simultaneous=True)
    same(F, diagonal, 'diagonal equivalence')
    degrees = [S.Poly(f,x,y,z).total_degree() for f in F]
    terms = [len(S.Poly(f,x,y,z).terms()) for f in F]
    require(degrees == [7,6,4] and terms == [7,6,3], 'degree/term profile')
    passed('diagonal equivalence, degree profile (7,6,4), and 16 nonzero terms')

    rho = S.symbols('rho', nonzero=True)
    gamma, ell = a*b**2, 9*b
    first = {x:rho, y:0, z:-1/(gamma*rho**2)}
    second = {x:0, y:-ell/(gamma*rho), z:71/(gamma*rho**2)}
    target = S.Matrix([-1/(gamma*rho**2),-ell/(gamma*rho),0])
    same(F.subs(first, simultaneous=True), target, 'first collision point')
    same(F.subs(second, simultaneous=True), target, 'second collision point')
    passed('universal rational collision family for a*b*rho != 0')

    same(F.subs(a,0),S.Matrix([z,y+9*b*x*z,x]),'a=0 shear')
    same(F.subs(b,0),S.Matrix([z-rat(8,9)*a*y*y,y,x]),'b=0 shear')
    passed('both parameter axes specialize to the displayed tame automorphisms')

    H = S.Function('H')
    lam, U, V, W = S.symbols('lambda U V W')
    tame = S.Matrix([z+y*y*H(x*y),y+lam*x*(z+y*y*H(x*y)),x])
    iy = V-lam*W*U
    inverse = S.Matrix([W,iy,U-iy**2*H(W*iy)])
    same(tame.subs(dict(zip(variables,inverse)), simultaneous=True),
         S.Matrix([U,V,W]),'tame right inverse')
    same(inverse.subs(dict(zip([U,V,W],tame)), simultaneous=True),
         variables,'tame left inverse')
    passed('two-sided inverse identity for the entire constant-r family')

    ss = S.symbols('s')
    A,B,C,D,Ap,Bp,Cp,Dp = S.symbols('A B C D Ap Bp Cp Dp')
    beta = S.symbols('beta')
    P,Q = A*ss+B,C*ss+D
    jchart = S.det(S.Matrix([
        [-2*P,Ap*ss+A*beta+Bp,A],
        [-Q,Cp*ss+C*beta+Dp,C],
        [ss,beta,1]
    ]))
    e0 = D*Bp-2*B*Dp
    e1 = D*Ap+2*C*Bp-3*A*Dp-2*B*Cp
    e2 = 2*C*Ap-3*A*Cp
    zero(jchart-(e0+e1*ss+e2*ss**2),'three coefficient identities')
    passed('three one-variable determinant identities used in the all-degree proof')

    E = 1-rat(2,3)*beta*t
    an,cn = E**3,9*E**2/beta
    bn,dn = -1+beta*t-rat(2,9)*beta**2*t**2,4*t-9/beta
    endpoint = {A:an,B:bn,C:cn,D:dn,
        Ap:S.diff(an,t),Bp:S.diff(bn,t),Cp:S.diff(cn,t),Dp:S.diff(dn,t)}
    zero(e0.subs(endpoint)+1,'endpoint e0')
    zero(e1.subs(endpoint),'endpoint e1')
    zero(e2.subs(endpoint),'endpoint e2')
    same(S.Matrix([p,q,r]).subs({a:beta**2,b:1/beta},simultaneous=True),
         S.Matrix([an*(1+beta*t+v)+bn,cn*(1+beta*t+v)+dn,1+beta*t+v]),
         'classification endpoint family')
    passed('all-degree proof endpoint and reparametrization')

    # A source shear handles arbitrary polynomial t-dependence in r.
    hf = S.Function('h')
    shear = S.Matrix([x,y,z+y*y*hf(x*y)])
    inverse_shear = S.Matrix([x,y,z-y*y*hf(x*y)])
    zero(shear.jacobian(variables).det()-1,'source shear determinant')
    same(shear.subs(dict(zip(variables,inverse_shear)),simultaneous=True),
         variables,'source shear inverse')
    for degree_h in range(4):
        extended = F.subs(z,z+y*y*(x*y)**degree_h)
        actual = [S.Poly(S.expand(f),x,y,z).total_degree() for f in extended]
        require(actual == [2*degree_h+8,2*degree_h+7,2*degree_h+5],
                'extended-family degree profile')
    passed('triangular extension: shear identity and degree profiles for h=1,t,t^2,t^3')

    cs = S.symbols('p20 p11 p30 p21 p40 p31 q01 q20 q11 q30 q21 q40')
    p20,p11,p30,p21,p40,p31,q01,q20,q11,q30,q21,q40 = cs
    pp = v+p20*t**2+p11*t*v+p30*t**3+p21*t**2*v+p40*t**4+p31*t**3*v
    qq = t+q01*v+q20*t**2+q11*t*v+q30*t**3+q21*t**2*v+q40*t**4
    # Normalize variable beta,gamma over their unit locus, without assuming
    # reduced coefficients. This underlies the torus-times-double-point result.
    be,ga = S.symbols('beta gamma', nonzero=True)
    p_normal = ga*pp.subs({t:t/be,v:v/ga},simultaneous=True)
    q_normal = be*qq.subs({t:t/be,v:v/ga},simultaneous=True)
    rr = 1+be*t+ga*v
    zero(det_reduced(p_normal,q_normal,1+t+v)
         -det_reduced(pp,qq,rr).subs({t:t/be,v:v/ga},simultaneous=True),
         'variable-r scheme normalization determinant')
    zero(p_normal.subs({t:be*t,v:ga*v},simultaneous=True)/ga-pp,
         'variable-r p normalization inverse')
    zero(q_normal.subs({t:be*t,v:ga*v},simultaneous=True)/be-qq,
         'variable-r q normalization inverse')
    passed('variable-r coefficient scheme: exact invertible torus normalization')

    polynomial = S.Poly(det_reduced(pp,qq,1+t+v)+1,t,v)
    monomials,equations = polynomial.monoms(),polynomial.coeffs()
    point = S.Matrix([-rat(8,9),-2,rat(28,27),rat(4,3),-rat(8,27),
                      -rat(8,27),9,-8,-12,4,4,0])
    point_sub = dict(zip(cs,point))
    require(len(equations)==18,'number of coefficient equations')
    for equation in equations:
        zero(equation.subs(point_sub),'normalized point')
    M = S.Matrix(equations).jacobian(cs).subs(point_sub)
    tangent = S.Matrix([-7,-18,18,24,-8,-8,162,-198,-324,144,144,0])/144
    same(M*tangent,S.zeros(18,1),'tangent kernel')
    rows = [0,2,4,5,6,9,11,12,13,15,17]
    cols = [i for i in range(12) if i != 10]
    minor = M.extract(rows,cols).det()
    require(minor == -18874368,'rank minor')
    require(M.rank() == 11,'Jacobian rank')
    passed('coefficient scheme has tangent dimension one; exact rank minor verified')

    eps = S.symbols('eps')
    tangent_sub = {c:base_value+eps*direction
                   for c,base_value,direction in zip(cs,point,tangent)}
    residuals = [S.expand(f.subs(tangent_sub,simultaneous=True)) for f in equations]
    obstruction = S.Matrix([f.coeff(eps,2) for f in residuals])
    for f in residuals:
        zero(f.subs(eps,0),'constant residual')
        zero(f.coeff(eps,1),'linear residual')
    cokernel = S.Matrix([-205,0,-46,0,-40,24,-8,0,4,0,0,0,0,0,0,0,0,0])
    same(cokernel.T*M,S.zeros(1,12),'cokernel identity')
    pairing = (cokernel.T*obstruction)[0]
    require(pairing == -rat(1,72),'second-order obstruction pairing')
    passed('nonzero first-order deformation is obstructed at second order: -1/72')

    h = q21-4
    generators = [cs[i]-point[i]-tangent[i]*h for i in range(12) if i != 10]+[h*h]
    substitution = {cs[i]:point[i]+tangent[i]*h for i in range(12) if i != 10}
    quotients = []
    for f in equations:
        red = S.expand(f.subs(substitution,simultaneous=True))
        quotient,rem = S.div(red,h*h,q21)
        zero(rem,'double-point ideal containment')
        quotients.append(quotient)
    passed('all 18 equations vanish under the exact dual-number presentation')

    payload: dict[str,Any] = {
        'title':'All-Degree Rigidity of a Weighted Keller Class',
        'repository_commit':'e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9',
        'python_version':platform.python_version(), 'sympy_version':S.__version__,
        'arithmetic':'exact rational / symbolic; no numerical tolerance',
        'checks':checks,'family':{'p':str(p),'q':str(q),'r':str(r)},
        'coordinates':[str(c) for c in cs], 'base':[str(c) for c in point],
        'equation_monomials':[list(m) for m in monomials],
        'equations':[str(f) for f in equations],
        'jacobian_matrix':[[str(M[i,j]) for j in range(M.cols)] for i in range(M.rows)],
        'tangent':[str(c) for c in tangent],
        'minor':{'rows_zero_based':rows,'columns_zero_based':cols,'determinant':str(minor)},
        'obstruction':[str(c) for c in obstruction],
        'cokernel_functional':[str(c) for c in cokernel],
        'obstruction_pairing':str(pairing),
        'double_point_generators':[str(f) for f in generators],
        'equations_mod_linear_relations_divided_by_h_squared':[str(c) for c in quotients],
        'trust_boundary':'Finite identities only. The all-degree classification and reverse ideal containment use the article proofs. No Lean/Rocq verification claimed.'
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload,indent=2)+'\n',encoding='utf-8')
    print(f'\nAll {len(checks)} check groups passed. Certificate: {args.output}')


if __name__ == '__main__':
    main()
