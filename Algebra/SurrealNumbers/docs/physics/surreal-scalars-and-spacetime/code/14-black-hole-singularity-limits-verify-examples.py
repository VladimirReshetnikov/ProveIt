#!/usr/bin/env python3
"""Symbolic checks accompanying 'Surreal Scalars and Black-Hole Singularities'.

Requires Python 3.10+ and SymPy. Run: python verify_examples.py
These finite symbolic checks are not a formal proof of the article, a check of
Lean files, or a simulation of a physical singularity.
"""
from __future__ import annotations
import sys
from time import perf_counter
try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit('Install the required package: python -m pip install sympy') from exc

CHECKS: list[str] = []

def zero(label: str, expression: sp.Expr) -> None:
    result = sp.simplify(sp.trigsimp(expression))
    if result != 0:
        raise AssertionError(f'{label}: nonzero residual {result}')
    CHECKS.append(label)
    print(f'PASS  {label}')


def run() -> None:
    start = perf_counter()
    r, m, ell, s, j = sp.symbols('r m ell s j', positive=True)
    th, t, ph = sp.symbols('theta t phi', real=True)
    f = sp.Function('f')(r)
    coords = [t, r, th, ph]
    diag = [-f, 1/f, r**2, r**2*sp.sin(th)**2]
    n = 4
    # Diagonal-coordinate Levi-Civita connection, then R^a_{bcd}.
    gamma: dict[tuple[int, int, int], sp.Expr] = {}
    for a in range(n):
        for b in range(n):
            for c in range(n):
                val = ((sp.diff(diag[a], coords[b]) if a == c else 0)
                       + (sp.diff(diag[a], coords[c]) if a == b else 0)
                       - (sp.diff(diag[b], coords[a]) if b == c else 0))/(2*diag[a])
                val = sp.simplify(val)
                if val != 0:
                    gamma[a, b, c] = val
    def G(a: int, b: int, c: int) -> sp.Expr:
        return gamma.get((a,b,c), sp.S.Zero)
    riemann: dict[tuple[int,int,int,int], sp.Expr] = {}
    for a in range(n):
        for b in range(n):
            for c in range(n):
                for d in range(n):
                    val = sp.diff(G(a,d,b), coords[c])-sp.diff(G(a,c,b), coords[d])
                    val += sum(G(a,c,k)*G(k,d,b)-G(a,d,k)*G(k,c,b) for k in range(n))
                    val = sp.simplify(sp.trigsimp(val))
                    if val != 0:
                        riemann[a,b,c,d] = val
    ricci = sp.Matrix(n,n,lambda b,d: sp.simplify(sum(
        riemann.get((a,b,a,d), sp.S.Zero) for a in range(n))))
    scalar = sp.simplify(sum(ricci[a,a]/diag[a] for a in range(n)))
    curvature = sp.simplify(sp.trigsimp(sum(
        diag[a]*val**2/(diag[b]*diag[c]*diag[d])
        for (a,b,c,d), val in riemann.items())))
    formula = sp.diff(f,r,2)**2+4*(sp.diff(f,r)/r)**2+4*((1-f)/r**2)**2
    zero('Kretschmann invariant from full Riemann tensor', curvature-formula)
    zero('Mixed Einstein component G^t_t', ricci[0,0]/diag[0]-scalar/2-(r*sp.diff(f,r)+f-1)/r**2)
    schwarz = 1-2*m/r
    zero('Schwarzschild K = 48 m^2/r^6', formula.subs(f,schwarz).doit()-48*m**2/r**6)
    for a in range(4):
        for b in range(a,4):
            zero(f'Schwarzschild Ricci[{a},{b}] = 0', ricci[a,b].subs(f,schwarz).doit())
    ef = sp.Matrix([[-schwarz,1,0,0],[1,0,0,0],[0,0,r**2,0],
                    [0,0,0,r**2*sp.sin(th)**2]])
    zero('Eddington-Finkelstein determinant', ef.det()+r**4*sp.sin(th)**2)
    zero('Finite horizon curvature', (48*m**2/r**6).subs(r,2*m)-sp.Rational(3,4)/m**4)
    radial = (sp.Rational(9,2)*m)**sp.Rational(1,3)*s**sp.Rational(2,3)
    zero('Radial E=1 first integral', sp.diff(radial,s)**2-2*m/radial)
    zero('Proper-time curvature K = 64/(27 s^4)', 48*m**2/radial**6-sp.Rational(64,27)/s**4)
    zero('Radial tidal coefficient', 2*m/radial**3-sp.Rational(4,9)/s**2)
    for p in [sp.Rational(4,3), -sp.Rational(1,3)]:
        zero(f'Radial Jacobi exponent {p}', sp.diff(s**p,s,2)-sp.Rational(4,9)*s**(p-2))
    for p in [sp.Rational(2,3), sp.Rational(1,3)]:
        zero(f'Transverse Jacobi exponent {p}', sp.diff(s**p,s,2)+sp.Rational(2,9)*s**(p-2))
    angular = (sp.Rational(5,2)*sp.sqrt(2*m)*j*s)**sp.Rational(2,5)
    zero('Nonradial leading balance', sp.diff(angular,s)**2-2*m*j**2/angular**3)
    R, E = sp.symbols('R E', positive=True)
    exact_v2 = E**2-(1-2*m/r)*(1+j**2/r**2)
    zero('Exact crossover integrand denominator factor',
         exact_v2.subs(r,j*R)/(2*m/j)*(R**3)
         -(1+R**2+j/(2*m)*((E**2-1)*R**3-R)))
    hayward = 1-2*m*r**2/(r**3+2*m*ell**2)
    kh = sp.factor(formula.subs(f,hayward).doit())
    zero('Hayward core curvature', sp.limit(kh,r,0)-24/ell**4)
    density = sp.simplify(-(r*sp.diff(hayward,r)+hayward-1)/(8*sp.pi*r**2))
    zero('Hayward core density', sp.limit(density,r,0)-3/(8*sp.pi*ell**2))
    zero('Hayward Schwarzschild limit at r>0', sp.limit(hayward,ell,0)-schwarz)
    eta, a, c = sp.symbols('eta a c')
    finite_part = sp.series(1/(eta+c*eta**2)+a,eta,0,1).removeO().coeff(eta,0)
    zero('Finite-part reparametrization shifts a to a-c', finite_part-(a-c))
    x = sp.symbols('x', positive=True)
    for N in range(1,9):
        y = sum(sp.factorial(k)*x**(-k-1) for k in range(N+1))
        zero(f'Factorial ODE residual, truncation N={N}',
             sp.diff(y,x)+y-1/x+sp.factorial(N+1)*x**(-N-2))
    zero('Exponentially small homogeneous ambiguity', sp.diff(sp.exp(-x),x)+sp.exp(-x))
    print(f'\n{len(CHECKS)} checks passed.')
    print(f'Python {sys.version.split()[0]}; SymPy {sp.__version__}.')
    print('Scope: finite symbolic identities only; no general analytic or physical validation.')
    print(f'Runtime: {perf_counter()-start:.2f} seconds.')

if __name__ == '__main__':
    run()
