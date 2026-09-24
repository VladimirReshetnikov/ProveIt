#!/usr/bin/env python3
"""Exact finite certificates for Low-Order Nonlinear Rigidity at Surreal Scales.

These tests check finite algebraic identities, not the infinite-support theorems,
historical priority, or proof-assistant correctness. Run with Python 3.9+ and SymPy.
"""
from __future__ import annotations
import json
import platform
from pathlib import Path
import sympy as sp

GROUPS: dict[str, int] = {}

def check(name: str, assertion: bool) -> None:
    if not assertion:
        raise AssertionError(name)
    GROUPS[name] = GROUPS.get(name, 0) + 1

def monomials_degree(variables, degree):
    if len(variables) == 1:
        return [variables[0] ** degree]
    result = []
    for j in range(degree + 1):
        result.extend(variables[0] ** j * m for m in monomials_degree(variables[1:], degree-j))
    return result

T,U,z,A,B,s,t,N = sp.symbols('T U z A B s t N')
y = sp.symbols('Y0:5')
E = lambda p: sp.expand(z*sp.diff(p,z))
def jet(p, r):
    out = [p]
    for _ in range(r):
        out.append(E(out[-1]))
    return out

def evaluate(h,p,r):
    return sp.expand(h.subs(dict(zip(y[:r+1],jet(p,r))), simultaneous=True))

# The homogeneous ideal of the conic: the rank is 2d+1.
for d in range(1, 10):
    mons = monomials_degree(y[:3],d)
    images = [sp.Poly(m.subs({y[0]:1,y[1]:T,y[2]:T**2}),T) for m in mons]
    mat = sp.Matrix([[p.nth(j) for p in images] for j in range(2*d+1)])
    check('conic_homogeneous_rank', mat.rank() == 2*d+1)
    check('conic_kernel_dimension', len(mons)-mat.rank() == d*(d-1)//2)

# No degree <=3 hypersurface is singular along the entire twisted cubic.
for d in range(1,4):
    mons = monomials_degree(y[:4],d)
    rows = []
    for j in range(4):
        images = [sp.Poly(sp.diff(m,y[j]).subs(dict(zip(y[:4],[1,T,T**2,T**3]))),T) for m in mons]
        rows.extend([[p.nth(k) for p in images] for k in range(3*(d-1)+1)])
    check('twisted_cubic_gradient_injectivity', sp.Matrix(rows).rank() == len(mons))
    # Every curve-vanishing homogeneous form has a first polar with (U-T)^2.
    images = [sp.Poly(m.subs(dict(zip(y[:4],[1,T,T**2,T**3]))),T) for m in mons]
    mat = sp.Matrix([[p.nth(k) for p in images] for k in range(3*d+1)])
    for vec in mat.nullspace():
        h = sum(c*m for c,m in zip(vec,mons))
        polar = sp.expand(sum(sp.diff(h,y[j]).subs(dict(zip(y[:4],[1,T,T**2,T**3])))*U**j for j in range(4)))
        q,r = sp.div(polar,(U-T)**2,U)
        check('first_polar_double_factor',sp.expand(r)==0)
        check('first_polar_remaining_degree',sp.degree(q,U)<=1)

secant = sp.Matrix([A+B,A*s+B*t,A*s**2+B*t**2,A*s**3+B*t**3])
check('secant_jacobian',sp.factor(secant.jacobian([A,B,s,t]).det()) == -A*B*(s-t)**4)

Hc=y[0]**2*y[3]-4*y[0]*y[1]*y[2]+3*y[1]**3
polar=sp.expand(sum(sp.diff(Hc,y[j]).subs(dict(zip(y[:4],[1,T,T**2,T**3])))*U**j for j in range(4)))
check('cubic_polar_example',sp.expand(polar-(U-T)**2*(U-2*T))==0)

S=y[0]*y[2]-y[1]**2
for m in range(0,10):
    for n in range(m+1,m+7):
        p=2*z**m+3*z**n+5*z**(n+2)
        val=evaluate(S,p,2)
        check('conic_lowest_cross_term',sp.Poly(val,z).nth(m+n)==6*(n-m)**2)

H3=2*y[0]**2*y[3]**2-13*y[0]*y[1]*y[2]*y[3]+9*y[0]*y[2]**3+9*y[1]**3*y[3]-7*y[1]**2*y[2]**2
Q4=-2*y[0]*y[4]+9*y[1]*y[3]-7*y[2]**2
an=2*y[0]*N**2-3*y[1]*N+y[2]
bn=2*y[1]*N**2-3*y[2]*N+y[3]
check('quartic_resultant',sp.expand(sp.resultant(an,bn,N)-2*H3)==0)
for j in range(4):
    check('quartic_singular_on_twisted_cubic',sp.expand(sp.diff(H3,y[j]).subs(dict(zip(y[:4],[1,T,T**2,T**3]))))==0)
for n in range(1,13):
    for a,b in [(1,1),(2,3),(-3,4)]:
        p=a*z**n+b*z**(2*n)
        check('quartic_binomials',evaluate(H3,p,3)==0)
        check('fourth_order_binomials',evaluate(Q4,p,4)==0)

kernel=-2*(s**4+t**4)+9*(s*t**3+t*s**3)-14*s**2*t**2
check('fourth_order_pair_kernel',sp.expand(kernel-(s-t)**2*(s-2*t)*(t-2*s))==0)
q=sp.symbols('q')
f=q*z+q**4*z**2+q**16*z**4+q**64*z**8
check('hidden_residual_z5',sp.Poly(evaluate(Q4,f,4),z).nth(5)==-126*q**17)

# Finite Newton windows: exact crossing slopes for n^2 and for powers of two.
for n in range(1,40):
    delta=2*n+1
    costs={j:j*j-j*delta for j in range(0,85)}
    active=[j for j,c in costs.items() if c==min(costs.values())]
    check('quadratic_newton_transition',active==[n,n+1])
for j in range(0,12):
    n=2**j
    delta=3*n
    indices=[2**k for k in range(0,14)]
    costs={k:k*k-k*delta for k in indices}
    active=[k for k,c in costs.items() if c==min(costs.values())]
    check('doubling_newton_transition',active==[n,2*n])

# Finite checks of the mixed coefficient formula, including complex coefficients.
forms=[Hc, y[0]*y[2]-y[1]**2, y[0]*y[3]-y[1]*y[2], y[1]*y[3]-y[2]**2]
for h in forms:
    d=sp.Poly(h,*y[:4]).total_degree()
    for m in range(1,6):
        n=m+2
        p=2*z**m+3*z**n+7*z**(n+5)
        vals=[1,sp.Integer(m),sp.Integer(m)**2,sp.Integer(m)**3]
        polar_mn=sum(sp.diff(h,y[j]).subs(dict(zip(y[:4],vals)))*n**j for j in range(4))
        actual=sp.Poly(evaluate(h,p,3),z).nth((d-1)*m+n)
        check('first_polar_lowest_coefficient',sp.expand(actual-2**(d-1)*3*polar_mn)==0)

report={
    'status':'passed',
    'python':platform.python_version(),
    'sympy':sp.__version__,
    'total_assertions':sum(GROUPS.values()),
    'groups':GROUPS,
    'scope':'Exact finite algebra and finite Newton windows only. No Lean verification; no certification of infinite-support arguments or novelty.'
}
out=Path(__file__).resolve().parent.parent/'data'/'verification.json'
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
