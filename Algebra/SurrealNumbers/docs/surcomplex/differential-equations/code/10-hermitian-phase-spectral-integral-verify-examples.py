#!/usr/bin/env python3
"""Exact finite checks for the accompanying article.

Requires Python 3.10+ and SymPy.  These checks do not verify the general
surreal, differential-field, or infinite-support theorems.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s

x = s.symbols('x', positive=True)
t = s.symbols('t', real=True)
i = s.I
checks: list[str] = []

def zero(expr: s.Expr | s.MatrixBase, name: str) -> None:
    entries = list(expr) if isinstance(expr, s.MatrixBase) else [expr]
    for e in entries:
        if s.simplify(s.expand(e)) != 0:
            raise AssertionError(f'{name}: nonzero residual {s.simplify(e)}')
    checks.append(name)

def gauge(P: s.Matrix, B: s.Matrix) -> s.Matrix:
    return s.simplify(P.diff(x)*P.inv() + P*B*P.inv())

# A nonnormal pure gauge with instantaneous eigenvalues +i and -i.
P = s.Matrix([[1-x*x,x],[-x,1]])
A = s.Matrix([[-x,1+x*x],[-1,x]])
zero(P.det()-1, 'nonnormal: unimodular gauge')
zero(P.diff(x)-A*P, 'nonnormal: trivial differential system')
z = s.symbols('z')
zero(A.charpoly(z).as_expr()-(z*z+1), 'nonnormal: eigenvalues plus/minus i')

# A genuinely nontriangular skew-Hermitian example.
a = (1-x*x)/(1+x*x)
b = 2*x/(1+x*x)
U = s.Matrix([[a,-b],[b,a]])
D = s.diag(i*x,i/x)
A = gauge(U,D)
zero(U.T*U-s.eye(2), 'unitary example: orthogonality')
zero(A.conjugate().T+A, 'unitary example: skew-Hermiticity')
zero(U.T*A*U-U.T*U.diff(x)-D, 'unitary example: exact phase gauge')
H = -i*A
zero(H.det()-(1-4/(1+x*x)**2), 'unitary example: instantaneous determinant')

# A damped/growing Jordan system has a positive, nonconstant invariant metric.
A = s.Matrix([[1,1],[0,1]])
G = s.exp(-2*x)*s.Matrix([[1,-x],[-x,x*x+1]])
zero(G.diff(x)+A.T*G+G*A, 'Jordan: differential metric identity')
zero(G.det()-s.exp(-4*x), 'Jordan: positive determinant identity')

# A coupled three-dimensional system, including its toric first integrals.
P = s.Matrix([[1,1/x,0],[0,1,1/x**2],[0,0,1]])
D = s.diag(i,i,-2*i)
A = gauge(P,D)
G = s.simplify(P.inv().conjugate().T*P.inv())
zero(G.diff(x)+A.conjugate().T*G+G*A, 'three phases: invariant Hermitian metric')
zero(P.diff(x)-A*P+P*D, 'three phases: gauge identity')
y = s.symbols('y1:4')
Y = s.Matrix(y)
Z = P.inv()*Y
F = [Z[0]**2*Z[2],Z[0]*Z[1]*Z[2],Z[1]**2*Z[2]]
def total(f: s.Expr) -> s.Expr:
    return s.diff(f,x)+sum(s.diff(f,y[j])*(A*Y)[j] for j in range(3))
for j,f in enumerate(F):
    zero(total(f),f'three phases: polynomial first integral {j+1}')
zero(F[0]*F[2]-F[1]**2,'three phases: quadratic relation')

# Noncommutative, normalized near-identity integration.
X = s.Matrix([[0,i],[i,0]])
Y2 = s.diag(i,-i)
N = 12
C = [s.eye(2)]
for n in range(N):
    C.append(s.simplify((X*C[n]+(2*Y2*C[n-1] if n else s.zeros(2)))/(n+1)))
for n in range(N):
    zero((n+1)*C[n+1]-X*C[n]-(2*Y2*C[n-1] if n else s.zeros(2)),
         f'noncommutative recurrence {n}')
for n in range(1,N+1):
    zero(sum((C[j].conjugate().T*C[n-j] for j in range(n+1)),s.zeros(2)),
         f'noncommutative unitarity coefficient {n}')
naive3 = X**3/s.Integer(6)+(X*Y2+Y2*X)/2
zero(C[3]-naive3-(Y2*X-X*Y2)/6,'noncommutative: first naive-exponential defect')
assert Y2*X-X*Y2 != s.zeros(2)
checks.append('noncommutative: defect is genuinely nonzero')

# Airy amplitude: a=x^(-1/4) sum c_n x^(-3n/2).
N = 16
c = [s.Integer(1)]
for n in range(N):
    c.append(s.simplify(-i*s.Rational((6*n+1)*(6*n+5),48*(n+1))*c[-1]))
for n in range(N):
    alpha = -s.Rational(1,4)-s.Rational(3*n,2)
    zero(alpha*(alpha-1)*c[n]-3*i*(n+1)*c[n+1],f'Airy recurrence {n}')
# Let u=x^(-3/2).  |sum c_n u^n|^2 and its square root are exact jets.
u = s.symbols('u', real=True)
f = sum(c[n]*u**n for n in range(N+1))
prod = s.Poly(s.expand(f*s.conjugate(f)),u)
rhojet = s.series(s.sqrt(sum(prod.nth(n)*u**n for n in range(9))),u,0,9).removeO()
zero(rhojet.coeff(u,2)+s.Rational(5,64),'Airy: first amplitude correction')
# A rational-power polynomial is enough for a jet residual certificate.
a_trunc = sum(c[n]*x**(-s.Rational(1,4)-s.Rational(3*n,2)) for n in range(N+1))
alpha = -s.Rational(1,4)-s.Rational(3*N,2)
res = s.diff(a_trunc,x,2)+2*i*s.sqrt(x)*s.diff(a_trunc,x)+i/(2*s.sqrt(x))*a_trunc
zero(res-alpha*(alpha-1)*c[N]*x**(alpha-2),'Airy: exact truncation residual')

# Ermakov-Pinney / metric equivalence with arbitrary symbolic jets.
r,r1,r2,q = s.symbols('r r1 r2 q', real=True, nonzero=True)
M = s.Matrix([[r1*r1+r**-2,-r*r1],[-r*r1,r*r]])
A = s.Matrix([[0,1],[-q,0]])
Md = M.diff(r)*r1+M.diff(r1)*r2
zero(M.det()-1,'Pinney: determinant-one identity')
zero((Md+A.T*M+M*A).subs(r2,r**-3-q*r),'Pinney: invariant metric identity')
S = s.Matrix([[r,0],[r1,1/r]])
Sd = S.diff(r)*r1+S.diff(r1)*r2
J = s.Matrix([[0,1],[-1,0]])
zero((S.inv()*A*S-S.inv()*Sd).subs(r2,r**-3-q*r)-r**-2*J,
     'Pinney: symplectic amplitude reduction')

report = {
    'status':'PASS', 'number_of_checks':len(checks),
    'sympy_version':s.__version__, 'checks':checks,
    'airy_amplitude_unit_jet':str(rhojet),
    'three_phase_matrix':str(s.simplify(gauge(s.Matrix([[1,1/x,0],[0,1,1/x**2],[0,0,1]]),s.diag(i,i,-2*i)))),
    'scope':'Finite exact symbolic checks; not a proof of general or infinite-support theorems.'
}
root = Path(__file__).resolve().parents[1]
(root/'data').mkdir(exist_ok=True)
(root/'data'/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['status','number_of_checks','sympy_version','airy_amplitude_unit_jet','three_phase_matrix']},indent=2))
