#!/usr/bin/env python3
"""Exact finite checks for Surreal-Valued Fields on Minkowski Space.

These checks audit signs and finite identities. They do not implement Hahn
summation, establish analytic existence, or constitute Lean formalization.
Requires Python 3.10+ and SymPy. Run: python verification/check_identities.py
"""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import sympy as s

RESULTS: list[dict[str, str]] = []

def check(name: str, expression: object) -> None:
    if isinstance(expression, s.MatrixBase):
        ok = all(s.simplify(e) == 0 for e in expression)
    elif isinstance(expression, (list, tuple)):
        ok = all(s.simplify(e) == 0 for e in expression)
    else:
        ok = s.simplify(expression) == 0
    if not ok:
        raise AssertionError(f"Failed: {name}: {expression}")
    RESULTS.append({"name": name, "status": "PASS"})
    print(f"PASS  {name}")

eta = s.diag(1, -1, -1, -1)
lam = s.symbols('lam', positive=True)
eps = s.symbols('eps', positive=True)
a = (lam + 1/lam)/2
b = (lam - 1/lam)/2
L = s.Matrix([[a,b,0,0],[b,a,0,0],[0,0,1,0],[0,0,0,1]])
check('Lorentz boost preserves eta', L.T*eta*L-eta)
check('Lorentz boost determinant is one', L.det()-1)
kp = s.Matrix([1,1,0,0]); km = s.Matrix([1,-1,0,0])
check('Null boost eigenvectors', list(L*kp-lam*kp)+list(L*km-km/lam))
check('Infinite boost reveals infinitesimal null vector', L.subs(lam,1/eps)*(eps*kp)-kp)

E = s.Matrix(s.symbols('E1:4', real=True))
B = s.Matrix(s.symbols('B1:4', real=True))
F = s.zeros(4)  # both indices down
for i in range(3):
    F[0,i+1] = E[i]
    F[i+1,0] = -E[i]
    for j in range(3):
        F[i+1,j+1] = -sum(s.LeviCivita(i,j,k)*B[k] for k in range(3))
Fu = eta*F*eta
starF = s.zeros(4)
for i in range(4):
    for j in range(4):
        starF[i,j] = s.expand(sum(s.LeviCivita(i,j,k,l)*Fu[k,l]
                                    for k in range(4) for l in range(4))/2)
I = s.expand(sum(F[i,j]*Fu[i,j] for i in range(4) for j in range(4)))
J = s.expand(sum(F[i,j]*(eta*starF*eta)[i,j] for i in range(4) for j in range(4)))
check('Maxwell invariant F.F', I-2*(B.dot(B)-E.dot(E)))
check('Maxwell invariant F.starF', J-4*E.dot(B))
check('Hodge electric components', [starF[0,i+1]+B[i] for i in range(3)])
check('Hodge magnetic components', [starF[i+1,j+1]+sum(s.LeviCivita(i,j,k)*E[k]
    for k in range(3)) for i in range(3) for j in range(3)])
T = s.simplify(-Fu*eta*Fu.T + eta*I/4)
rho = (E.dot(E)+B.dot(B))/2
S = E.cross(B)
check('Maxwell stress symmetry', T-T.T)
check('Maxwell stress trace', s.trace(T*eta))
check('Maxwell positive energy density', T[0,0]-rho)
check('Maxwell energy flux', [T[0,i+1]-S[i] for i in range(3)])
check('Maxwell spatial stress', T[1:4,1:4] - (rho*s.eye(3)-E*E.T-B*B.T))
chi2 = (E.dot(E)-B.dot(B))**2/4 + E.dot(B)**2
check('Dominant-energy polynomial identity', rho**2-S.dot(S)-chi2)
check('Rainich stress square', (T*eta)**2-chi2*s.eye(4))
null_sub = {E[0]:s.Symbol('h'), E[1]:0,E[2]:0,B[0]:0,B[1]:s.Symbol('h'),B[2]:0}
kz = s.Matrix([1,0,0,1])
check('Null radiation stress', T.subs(null_sub)-s.Symbol('h')**2*kz*kz.T)
N = kp*(kp.T*eta)
check('Lorentz-self-adjoint null endomorphism', N.T*eta-eta*N)
check('Null endomorphism square', N*N)

# Hodge operator on every ordered exterior basis: basis I maps to
# (metric norm of I) * sign(I,J) * J, where J is its complement.
def star_basis(I: tuple[int, ...]) -> tuple[tuple[int, ...], s.Expr]:
    J = tuple(j for j in range(4) if j not in I)
    c = s.prod(eta[i,i] for i in I) * s.LeviCivita(*(I+J))
    return J,c
for p in range(5):
    for I0 in itertools.combinations(range(4),p):
        J0,c0 = star_basis(I0)
        I1,c1 = star_basis(J0)
        assert I0 == I1
        check(f'Hodge square degree {p}, basis {I0}', c0*c1-(-1)**(p*(4-p)+3))

# Differential identity for arbitrary smooth potential; no Maxwell equation
# is imposed: the current is defined by divergence of its field strength.
x = s.symbols('x0:4', real=True)
A = [s.Function(f'A{mu}')(*x) for mu in range(4)] # covariant components
Fd = s.Matrix(4,4,lambda mu,nu:s.diff(A[nu],x[mu])-s.diff(A[mu],x[nu]))
Fdu = eta*Fd*eta
Jd = s.Matrix([sum(s.diff(Fdu[mu,nu],x[mu]) for mu in range(4)) for nu in range(4)])
check('Current conservation from antisymmetry', sum(s.diff(Jd[mu],x[mu]) for mu in range(4)))
Id = sum(Fd[i,j]*Fdu[i,j] for i in range(4) for j in range(4))
Td = -Fdu*eta*Fdu.T+eta*Id/4
for nu in range(4):
    divergence = sum(s.diff(Td[mu,nu],x[mu]) for mu in range(4))
    force = sum(Fdu[nu,mu]*eta[mu,mu]*Jd[mu] for mu in range(4))
    check(f'Stress divergence + Lorentz force, component {nu}', s.expand(divergence+force))

# First nontrivial homogeneous nonlinear hierarchy: y'' + y^3 = 0,
# y(0)=eps, y'(0)=0. Rational symbolic recursion, through order eps^9.
tau = s.symbols('tau', real=True)
y = eps
coefs = {1:s.Integer(1)}
for n in range(2,10):
    rhs = -s.expand(y**3).coeff(eps,n)
    yn = s.integrate(s.integrate(rhs,(tau,0,tau)),(tau,0,tau))
    # Both definite integrals use their upper-variable primitive and are exact.
    coefs[n]=s.expand(yn)
    y += eps**n*yn
res = s.expand(s.diff(y,tau,2)+y**3)
check('Cubic wave/oscillator hierarchy through eps^9', [res.coeff(eps,n) for n in range(10)])
check('Cubic hierarchy initial displacement', y.subs(tau,0)-eps)
check('Cubic hierarchy initial velocity', s.diff(y,tau).subs(tau,0))

out = Path(__file__).with_name('verification_results.json')
record = {"sympy_version":s.__version__, "number_of_checks":len(RESULTS),
          "checks":RESULTS, "cubic_solution_through_order_9":str(s.expand(y)),
          "scope":"Exact finite identities only; not a proof of infinite support or PDE theorems."}
out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(f'\nAll {len(RESULTS)} exact checks passed. Written: {out.name}')
print('Cubic solution:', s.expand(y))
