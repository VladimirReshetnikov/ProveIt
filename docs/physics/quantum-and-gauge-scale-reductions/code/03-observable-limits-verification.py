#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex.

These tests do not formalize the general Hahn-support or elliptic theorems.
Requires Python >= 3.9 and SymPy. No network access, random data, or tolerances.
Run: python verification.py
"""
from __future__ import annotations

import platform
from typing import Dict, Tuple
import sympy as s

COUNT = 0


def check(name: str, value, expected=0) -> None:
    """Assert an exact scalar or finite-matrix identity and print its label."""
    global COUNT
    diff = value - expected
    entries = list(diff) if isinstance(diff, s.MatrixBase) else [diff]
    if any(s.simplify(s.expand(x)) != 0 for x in entries):
        raise AssertionError(f"FAILED: {name}\nDifference: {diff}")
    COUNT += 1
    print(f"PASS {COUNT:02d}: {name}")


def chi(q: Tuple[s.Expr, s.Expr, s.Expr, s.Expr]) -> s.Matrix:
    a, b, c, d = q
    z, w = a + s.I*b, c + s.I*d
    return s.Matrix([[z, w], [-s.conjugate(w), s.conjugate(z)]])


def qmul(q, r):
    a,b,c,d = q
    e,f,g,h = r
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)


def trunc(M: s.Matrix, z: s.Symbol, order: int) -> s.Matrix:
    """Truncate polynomial matrix entries; all arithmetic remains exact."""
    def entry(x):
        return sum((val*z**power[0] for power, val
                    in s.Poly(s.expand(x), z).terms()
                    if power[0] <= order), s.S.Zero)
    return M.applyfunc(entry)


def coefficient(M: s.Matrix, z: s.Symbol, n: int) -> s.Matrix:
    return M.applyfunc(lambda x: s.expand(x).coeff(z, n))


def quaternion_checks() -> None:
    print("\nQUATERNIONIC REPRESENTATION")
    a,b,c,d,e,f,g,h = s.symbols('a b c d e f g h', real=True)
    q,r = (a,b,c,d),(e,f,g,h)
    check('chi(q r) = chi(q) chi(r)', chi(qmul(q,r)), chi(q)*chi(r))
    check('chi(conj q) = chi(q)^*', chi((a,-b,-c,-d)), chi(q).conjugate().T)
    check('quaternion norm and matrix norm', chi(q).conjugate().T*chi(q),
          (a*a+b*b+c*c+d*d)*s.eye(2))
    qi, qj, qk = chi((0,1,0,0)), chi((0,0,1,0)), chi((0,0,0,1))
    check('[i,j] = 2k', qi*qj-qj*qi, 2*qk)
    check('trace doubles the real part', s.trace(chi(q)), 2*a)


def rare_event_checks() -> None:
    print("\nRARE EVENTS AND LEADING GRAM MATRICES")
    p,eps = s.symbols('p eps', positive=True)
    rho,sigma = s.diag(1-p,p,0),s.diag(1-p,0,p)
    P=s.diag(0,1,1)
    check('tagged example trace distance is p',
          s.trace(s.diag(0,p,p))/2, p)
    check('tagged branch success for rho', s.trace(P*rho*P), p)
    check('tagged branch success for sigma', s.trace(P*sigma*P), p)
    check('tagged conditional rho', P*rho*P/p, s.diag(0,1,0))
    check('tagged conditional sigma', P*sigma*P/p, s.diag(0,0,1))
    K=eps*s.Matrix([[1,0],[2,0]])
    R=s.diag(1,0)
    B=K*R
    X=B*B.T
    check('qubit branch probability',s.trace(X),5*eps**2)
    check('qubit conditional coherent state',X/s.trace(X),s.Matrix([[1,2],[2,4]])/5)
    B0=s.Matrix([[1,2,0],[0,1,1]])
    B1=s.Matrix([[0,1,2],[3,0,1]])
    B=eps**3*(B0+eps*B1)
    X=s.expand(B*B.T)
    check('Gram leading product at order six',coefficient(X,eps,6),B0*B0.T)
    check('positive Gram trace coefficient',s.trace(coefficient(X,eps,6)),7)
    check('normalized Gram residue trace',s.trace(B0*B0.T)/s.trace(B0*B0.T),1)


def three_level_checks() -> None:
    print("\nTHREE-LEVEL EFFECTIVE DYNAMICS")
    eps,Delta,r,lam,theta=s.symbols('eps Delta r lam theta',positive=True)
    low=(Delta-s.sqrt(Delta**2+4*eps**2*r**2))/2
    check('exact lower eigenvalue characteristic equation',low**2-Delta*low-eps**2*r**2)
    series=s.series(low,eps,0,10).removeO()
    expected=-eps**2*r**2/Delta+eps**4*r**4/Delta**3-2*eps**6*r**6/Delta**5+5*eps**8*r**8/Delta**7
    check('lower eigenvalue expansion through degree eight',series,expected)
    H=s.Matrix([[0,0,eps],[0,0,eps],[eps,eps,Delta]])
    check('full three-level characteristic polynomial',(lam*s.eye(3)-H).det(),lam*(lam**2-Delta*lam-2*eps**2))
    J=s.ones(2)
    V=s.eye(2)+(s.exp(2*s.I*theta)-1)*J/2
    check('bright-dark propagator is unitary',s.simplify(V.conjugate().T*V),s.eye(2))
    prob=s.expand(V[1,0]*s.conjugate(V[1,0]))
    check('transition probability is sin(theta)^2',s.expand_complex(prob),s.sin(theta)**2)


def graph_checks() -> None:
    print("\nNONCOMMUTING MATRIX GRAPH AND UNITARY BLOCK (DEGREE SIX)")
    z=s.symbols('z',real=True)
    N=6
    A1=s.Matrix([[1,2],[2,-1]])
    B1=s.Matrix([[2],[3]])
    C1=s.Matrix([[1]])
    D=s.Rational(5)
    coeff=[s.zeros(1,2) for _ in range(N+1)]
    coeff[1]=-B1.T/D
    for n in range(2,N+1):
        cubic=s.zeros(1,2)
        for r in range(1,n-1):
            cubic+=coeff[r]*B1*coeff[n-1-r]
        coeff[n]=(-C1*coeff[n-1]+coeff[n-1]*A1+cubic)/D
    X=sum((z**n*coeff[n] for n in range(1,N+1)),s.zeros(1,2))
    A,B,C=z*A1,z*B1,z*C1
    residual=B.T+(s.Matrix([[D]])+C)*X-X*A-X*B*X
    check('Riccati residual through degree six',trunc(residual,z,N),s.zeros(1,2))
    Y=trunc(X.T*X,z,N)
    invsqrt=s.eye(2)
    power=s.eye(2)
    for j in range(1,N//2+1):
        power=trunc(power*Y,z,N)
        invsqrt+=s.binomial(s.Rational(-1,2),j)*power
    Yhigh=trunc(X*X.T,z,N)
    high=s.ones(1)
    power=s.ones(1)
    for j in range(1,N//2+1):
        power=trunc(power*Yhigh,z,N)
        high+=s.binomial(s.Rational(-1,2),j)*power
    low=trunc(s.eye(2).col_join(X)*invsqrt,z,N)
    complement=trunc((-X.T).col_join(s.eye(1))*high,z,N)
    U=low.row_join(complement)
    H=A.row_join(B).col_join(B.T.row_join(s.Matrix([[D]])+C))
    check('normalized graph isometry through degree six',trunc(low.T*low,z,N),s.eye(2))
    check('full unitary normalization through degree six',trunc(U.T*U,z,N),s.eye(3))
    reduced=trunc(U.T*H*U,z,N)
    check('off-diagonal block vanishes through degree six',reduced[:2,2:3],s.zeros(2,1))
    Heff=reduced[:2,:2]
    check('effective block Hermiticity',Heff,Heff.T)
    check('first-order effective block',coefficient(Heff,z,1),A1)
    check('second-order virtual coupling',coefficient(Heff,z,2),-B1*B1.T/D)
    BB=B1*B1.T
    third=BB/(D**2)-(BB*A1+A1*BB)/(2*D**2)
    check('third-order normalization and coupling order',coefficient(Heff,z,3),third)


# A finite exterior algebra with matrix-valued polynomial coefficients.
# Keys use zero-based coordinate indices and are always sorted.
Form=Dict[Tuple[int,...],s.Matrix]
DIM=4
COORD=s.symbols('x1 x2 x3 x4',real=True)


def add(*forms: Form) -> Form:
    out: Form={}
    for form in forms:
        for key,val in form.items():
            if key not in out:out[key]=s.zeros(*val.shape)
            out[key]+=val
    return {k:v.applyfunc(s.expand) for k,v in out.items()}


def scale(c,form: Form) -> Form:
    return {key:c*val for key,val in form.items()}


def sign_and_key(indices):
    if len(set(indices))!=len(indices):return 0,()
    n=sum(indices[i]>indices[j] for i in range(len(indices)) for j in range(i+1,len(indices)))
    return (-1)**n,tuple(sorted(indices))


def wedge(a: Form,b: Form) -> Form:
    terms=[]
    for ka,va in a.items():
        for kb,vb in b.items():
            sign,key=sign_and_key(ka+kb)
            if sign:terms.append({key:sign*va*vb})
    return add(*terms)


def exterior_d(a: Form) -> Form:
    terms=[]
    for key,val in a.items():
        for mu,x in enumerate(COORD):
            sign,k=sign_and_key((mu,)+key)
            if sign:terms.append({k:sign*val.diff(x)})
    return add(*terms)


def star(a: Form) -> Form:
    out={}
    for key,val in a.items():
        complement=tuple(i for i in range(DIM) if i not in key)
        sign,_=sign_and_key(key+complement)
        out[complement]=sign*val
    return out


def trace_form(a: Form) -> Form:
    return {key:s.Matrix([[s.trace(val)]]) for key,val in a.items()}


def form_difference(a: Form,b: Form,size: int) -> Form:
    zero=s.zeros(size)
    return {k:(a.get(k,zero)-b.get(k,zero)).applyfunc(s.expand)
            for k in set(a)|set(b)}


def check_form(name: str,a: Form,b: Form,size: int=2) -> None:
    diff=form_difference(a,b,size)
    # Collect all entries in a single column, preserving each exact equation.
    entries=[x for key in sorted(diff) for x in diff[key]]
    check(name,s.Matrix(entries),s.zeros(len(entries),1))


def curvature(A: Form) -> Form:
    return add(exterior_d(A),wedge(A,A))


def gauge_checks() -> None:
    print("\nGAUGE CURVATURE, TRANSGRESSION, AND ACTION")
    x1,x2,x3,x4=COORD
    I,J,K=chi((0,1,0,0)),chi((0,0,1,0)),chi((0,0,0,1))
    A0={(1,):x1*I,(3,):x3*J}
    a={(0,):x2*K,(2,):x4*I,(1,):x1*x3*J}
    F0=curvature(A0)
    F=curvature(add(A0,a))
    Da=add(exterior_d(a),wedge(A0,a),wedge(a,A0))
    check_form('curvature expansion with correct graded sign',F,add(F0,Da,wedge(a,a)))
    lhs=add(trace_form(wedge(F,F)),scale(-1,trace_form(wedge(F0,F0))))
    trans=trace_form(add(scale(2,wedge(a,F0)),wedge(a,Da),scale(s.Rational(2,3),wedge(wedge(a,a),a))))
    rhs=exterior_d(trans)
    check_form('nonconstant noncommutative Chern-Weil transgression',lhs,rhs,size=1)
    if not any(s.expand(v[0]) != 0 for v in lhs.values()):
        raise AssertionError('Transgression test must be nontrivial.')
    print('      Nontriviality confirmed: the tested four-form is nonzero.')
    u,v=s.symbols('u v',real=True)
    At={(0,):u*I,(1,):v*J}
    Ft=curvature(At)
    expected={(0,1):2*u*v*K}
    check_form('constant torus nonabelian curvature',Ft,expected)
    zero4={(0,1,2,3):s.zeros(2)}
    check_form('torus charge density vanishes',wedge(Ft,Ft),zero4)
    norm=-s.trace(wedge(Ft,star(Ft))[(0,1,2,3)])
    check('torus action coefficient is eight',norm,8*u**2*v**2)
    Fplus=scale(s.Rational(1,2),add(Ft,star(Ft)))
    normplus=-s.trace(wedge(Fplus,star(Fplus))[(0,1,2,3)])
    check('harmonic self-dual defect norm is four',normplus,4*u**2*v**2)
    check('zero-charge action equals twice self-dual norm',norm,2*normplus)


def obstruction_toy_checks() -> None:
    print("\nFINITE-DIMENSIONAL KURANISHI TOY (NOT AN ELLIPTIC CHECK)")
    u=s.symbols('u',real=True)
    y=-u**2/(1+u)
    check('exact toy fixed-point equation',y+u**2+u*y)
    kappa=u**2+y**2
    check('toy obstruction closed form',kappa,u**2+u**4/(1+u)**2)
    yseries=s.series(y,u,0,12).removeO()
    check('toy recursion residual through degree eleven',s.series(yseries+u**2+u*yseries,u,0,12).removeO())
    check('quadratic leading obstruction is one',s.series(kappa,u,0,5).removeO().coeff(u,2),1)
    energy=s.series(2*kappa**2,u,0,7).removeO()
    check('toy leading action floor is two at degree four',energy.coeff(u,4),2)


def main() -> None:
    print('Exact finite symbolic verification for article.tex')
    print('Python:',platform.python_version())
    print('SymPy:',s.__version__)
    print('No floating-point tolerances; no external services used.')
    quaternion_checks()
    rare_event_checks()
    three_level_checks()
    graph_checks()
    gauge_checks()
    obstruction_toy_checks()
    print(f'\nSUCCESS: {COUNT} exact finite checks passed.')
    print('Scope: selected finite identities only; not formal proofs of general theorems.')


if __name__=='__main__':
    main()
