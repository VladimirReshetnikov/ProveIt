#!/usr/bin/env python3
"""Finite exact checks accompanying the article.

These checks do not formalize the Berarducci--Mantova derivation, prove
nonexistence, or validate arbitrary Hahn supports. They check displayed
finite identities and certified finite jets using SymPy exact arithmetic.
Run: python verify_examples.py
"""
from __future__ import annotations
import json
import platform
from pathlib import Path
from collections import Counter
import sympy as s

x, t, u, z, w = s.symbols('x t u z w', positive=True)
I = s.I
counts: Counter[str] = Counter()

def check(group: str, condition: bool, detail: str) -> None:
    if not condition:
        raise AssertionError(f'{group}: {detail}')
    counts[group] += 1

def zero(expr: s.Expr) -> bool:
    return s.simplify(s.expand(expr)) == 0

def deriv(expr: s.Expr) -> s.Expr:
    return s.expand(-t**2 * s.diff(expr, t))

def laurent_valuation(expr: s.Expr):
    expr = s.expand(expr)
    if expr == 0:
        return s.oo
    return min(int(term.as_powers_dict().get(t, 0)) for term in s.Add.make_args(expr))

def jet_total(expr: s.Expr, degree: int) -> s.Expr:
    poly = s.Poly(s.expand(expr), t, u)
    return s.expand(sum(coef*t**a*u**b for (a,b),coef in poly.terms() if a+b <= degree))

# Ordinary symbolic identities for primitives. Only finite-phase cases are
# used as surcomplex multiplicative solutions in the article.
for p in [-2, -1, 0, 1, 2, 3, 4]:
    B = s.log(x) if p == 1 else x**(1-p)/s.Integer(1-p)
    check('power_primitives', zero(s.diff(B, x)-x**(-p)), f'p={p}')
    if p > 1:
        y = s.exp(I*B)
        check('finite_phase_formulas', zero(s.diff(y,x)-I*x**(-p)*y), f'p={p}')

for k in range(3):
    L = [x]
    for _ in range(k+1):
        L.append(s.log(L[-1]))
    prefix = s.prod(L[:k])
    for p in [-1, 0, 1, 2, 3]:
        b = 1/(prefix*L[k]**p)
        B = L[k+1] if p == 1 else L[k]**(1-p)/s.Integer(1-p)
        check('logarithmic_primitives', zero(s.diff(B,x)-b), f'k={k}, p={p}')

# Laurent resolvents: Q(D)c with P(s)Q(s)=1+O(s^(N+1)).
N = 12
r = s.Symbol('r')
operators = [r-I, 1+r**2, 2+3*r-r**2]
inputs = [t, t**(-3)+1+2*t-3*t**4, 2*t**(-1)+I*t**2+t**5]
for P in operators:
    q = s.series(1/P, r, 0, N+1).removeO()
    for c in inputs:
        Ds = [c]
        for _ in range(N):
            Ds.append(deriv(Ds[-1]))
        y = s.expand(sum(q.coeff(r,n)*Ds[n] for n in range(N+1)))
        applied = s.Integer(0)
        yj = y
        for j in range(s.degree(P,r)+1):
            if j:
                yj = deriv(yj)
            applied += s.expand(P).coeff(r,j)*yj
        residual = s.expand(applied-c)
        check('laurent_resolvents', laurent_valuation(residual) >= laurent_valuation(c)+N+1,
              f'P={P}, c={c}')

y_display = sum(I**(n+1)*s.factorial(n)*t**(n+1) for n in range(N+1))
check('laurent_resolvents', laurent_valuation(deriv(y_display)-I*y_display-t) >= N+2,
      'displayed factorial expansion')

# A genuinely noncommuting two-scale system X_z=(t*Nmat+u*z*Mmat)X.
Nmat = s.Matrix([[0,1],[0,0]])
Mmat = s.Matrix([[0,0],[1,0]])
check('matrix_coefficients', Nmat*Mmat != Mmat*Nmat, 'noncommutativity')
K = 6
X: dict[tuple[int,int], s.Matrix] = {(0,0): s.eye(2)}
for degree in range(1, K+1):
    for p in range(degree+1):
        q = degree-p
        rhs = s.zeros(2)
        if p:
            rhs += Nmat*X[p-1,q]
        if q:
            rhs += z*Mmat*X[p,q-1]
        value = rhs.applyfunc(lambda e: s.integrate(e,z))
        value = value-value.subs(z,0)
        X[p,q] = value
        check('matrix_coefficients', value.diff(z) == rhs, f'ODE coefficient {p,q}')
        check('matrix_coefficients', value.subs(z,0) == s.zeros(2), f'initial coefficient {p,q}')
check('matrix_coefficients', X[1,1] == z**3*(Nmat*Mmat/s.Integer(6)+Mmat*Nmat/s.Integer(3)),
      'mixed coefficient')
Xjet = s.zeros(2)
for (p,q), value in X.items():
    Xjet += t**p*u**q*value
res = Xjet.diff(z)-(t*Nmat+u*z*Mmat)*Xjet
for entry in res:
    check('matrix_jets', jet_total(entry,K) == 0, 'ODE total-degree jet')
check('matrix_jets', jet_total(Xjet.det()-1,K) == 0, 'Liouville determinant jet')

# Nonlinear coherent solution y=t/(1-t*z), checked by coefficients.
Ky = 12
yjet = sum(t**n*z**(n-1) for n in range(1,Ky+1))
res = s.expand(s.diff(yjet,z)-yjet**2)
for n in range(Ky+1):
    check('nonlinear_jets', zero(res.coeff(t,n)), f'coefficient {n}')
check('nonlinear_jets', yjet.subs(z,0) == t, 'initial condition')
check('nonlinear_jets', zero(s.diff(t/(1-t*z),z)-(t/(1-t*z))**2), 'rational identity')

# Infinitesimal monodromy: scalar exponential jets, not a global Exp on No[i].
Km = 6
M_t = sum((2*s.pi*I*t)**n/s.factorial(n) for n in range(Km+1))
M_u = sum((2*s.pi*I*u)**n/s.factorial(n) for n in range(Km+1))
M_tu = sum((2*s.pi*I*(t+u))**n/s.factorial(n) for n in range(Km+1))
check('monodromy_jets', jet_total(M_t*M_u-M_tu,Km) == 0, 'composition')
check('monodromy_jets', M_t.coeff(t,1) == 2*s.pi*I, 'nonzero leading change')

# Typed polynomial chain rule, coefficient derivation plus coordinate derivative.
F = t*w + t**2*w**2 + (1+t)*w**3
h = 1/t+t
lhs = deriv(F.subs(w,h))
rhs = (-t**2*s.diff(F,t)).subs(w,h)+deriv(h)*s.diff(F,w).subs(w,h)
check('chain_rule', zero(lhs-rhs), 'total chain rule')
check('chain_rule', zero(deriv((t*w).subs(w,1/t))), 't*omega=1')

report = {
    'status': 'PASS',
    'checks_passed': sum(counts.values()),
    'groups': dict(counts),
    'environment': {'python': platform.python_version(), 'sympy': s.__version__},
    'matrix_total_degree': K,
    'laurent_iteration_order': N,
    'nonlinear_t_order': Ky,
    'scope': 'Finite exact symbolic identities and finite jets only; not formal verification of the article.',
    'matrix_mixed_coefficient': str(X[1,1]),
    'factorial_solution_first_terms': str(s.expand(sum(I**(n+1)*s.factorial(n)*t**(n+1) for n in range(5))))
}
out = Path(__file__).with_name('verification_report.json')
out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
