#!/usr/bin/env python3
"""Exact finite checks for logarithmic trace transfer.

These examples are regression checks, not a proof of the general theorem.
Requires Python 3.10+ and SymPy. No network or repository reads.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as s

Q = s.Rational
I = s.I
cases = []
assertions = 0


def require(condition, explanation):
    global assertions
    assertions += 1
    if not bool(condition):
        raise AssertionError(explanation)


def equal(x, y):
    if isinstance(x, s.MatrixBase):
        return all(s.simplify(z) == 0 for z in x-y)
    return s.simplify(x-y) == 0


def display(x):
    if isinstance(x, s.MatrixBase):
        return [[str(v) for v in x.row(i)] for i in range(x.rows)]
    return str(x)


def record(name, **values):
    cases.append({'name': name, **{k: display(v) for k, v in values.items()}})


def basic_contract(T, e, d, c):
    require(d > 0 and c > 0, 'positive shared parameters')
    require(equal(e*e, e), 'idempotent')
    require(equal(e.H, e), 'orthogonal projection')
    require(equal(T*T.H, d*(s.eye(T.rows)+c*e)), 'two singular values relation')
    require(T.det() != 0, 'invertible T')


def weighted_check(T, e, A, pT):
    require(equal(A*T, T*A), 'A commutes with T')
    require(equal(A*T.H, T.H*A), 'A commutes with T adjoint')
    require(equal(s.trace(A*e), s.trace(A*pT)), 'weighted trace conclusion')


def main():
    # A rational, genuinely nonnormal, nondiagonalizable operator.
    T = s.Matrix([[1, Q(3,2)], [0,1]])
    e = s.Matrix([[Q(4,5), Q(2,5)], [Q(2,5), Q(1,5)]])
    d,c = Q(1,4), s.Integer(15)
    basic_contract(T,e,d,c)
    require(not equal(T*T.H,T.H*T), 'example is nonnormal')
    require(equal((T-s.eye(2))**2,s.zeros(2)), 'Jordan nilpotent square')
    require(T != s.eye(2), 'Jordan nilpotent is nonzero')
    require(T.eigenvals() == {s.Integer(1):2}, 'one repeated eigenvalue')
    require(s.simplify(s.log(1/d)/s.log(1+c)) == Q(1,2), 'logarithmic value')
    pT=T/2
    require(not equal(pT,e), 'trace identity is not an operator identity')
    weighted_check(T,e,s.eye(2),pT)
    record('nonnormal_repeated_root', T=T,e=e,d=d,c=c,p='X/2',
           projection_trace=s.trace(e),polynomial_trace=s.trace(pT),
           nonnormal_commutator=T*T.H-T.H*T)

    # Non-scalar and nonnormal A, mixing equal reducing blocks.
    for j,M in enumerate([
        s.Matrix([[2+I,3],[-1,4-2*I]]),
        s.Matrix([[0,1],[0,0]]),
        s.Matrix([[1,2-I],[3+I,-2]])
    ],1):
        TT=s.kronecker_product(s.eye(2),T)
        ee=s.kronecker_product(s.eye(2),e)
        A=s.kronecker_product(M,s.eye(2))
        basic_contract(TT,ee,d,c)
        weighted_check(TT,ee,A,TT/2)
        require(equal(s.trace(A*ee),s.trace(M)), 'multiplicity-space trace')
        require(A != s.trace(A)/4*s.eye(4), 'A is nonscalar')
        record('mixing_multiplicity_space_'+str(j),multiplicity_matrix=M,
               A_is_normal=equal(A*A.H,A.H*A),
               left=s.trace(A*ee),right=s.trace(A*(TT/2)))

    # Removing adjoint commutation invalidates the theorem.
    N=s.Matrix([[0,1],[0,0]])
    require(equal(N*T,T*N),'counterexample still commutes with T')
    require(not equal(N*T.H,T.H*N),'counterexample fails adjoint commutation')
    require(equal(s.trace(N*e),Q(2,5)),'counterexample projection trace')
    require(equal(s.trace(N*pT),0),'counterexample polynomial trace')
    record('counterexample_without_adjoint_commutation',A=N,
           projection_trace=s.trace(N*e),polynomial_trace=s.trace(N*pT),
           adjoint_commutator=N*T.H-T.H*N)

    # One positive moment does not determine the desired weighted trace.
    T1=s.diag(1,2); e1=s.diag(0,1); A1=s.diag(-2,1)
    basic_contract(T1,e1,s.Integer(1),s.Integer(3))
    require(equal(A1*T1,T1*A1) and equal(A1*T1.H,T1.H*A1),'double commutation')
    require(equal(s.trace(A1*T1),0),'same first moment as zero A')
    require(equal(s.trace(A1*e1),1),'different desired weighted trace')
    p1=(T1*T1-T1)/2
    weighted_check(T1,e1,A1,p1)
    require(equal(s.trace(A1*T1**2),2),'second moment distinguishes')
    record('first_moment_insufficient',T=T1,e=e1,A=A1,
           first_moment=s.trace(A1*T1),second_moment=s.trace(A1*T1**2),
           projection_trace=s.trace(A1*e1),p='(X^2-X)/2')

    # Even matching dimension/zeroth and first weighted moment is insufficient.
    T2=s.diag(1,2,-2); e2=s.diag(0,1,1); A2=s.diag(-4,3,1)
    basic_contract(T2,e2,s.Integer(1),s.Integer(3))
    require(equal(s.trace(A2),0),'zeroth moment matches zero A')
    require(equal(s.trace(A2*T2),0),'first moment matches zero A')
    require(equal(s.trace(A2*e2),4),'projection trace differs')
    p2=T2**3/12+T2**2/4-T2/3
    weighted_check(T2,e2,A2,p2)
    record('zeroth_and_first_moments_insufficient',T=T2,e=e2,A=A2,
           zeroth=s.trace(A2),first=s.trace(A2*T2),
           second=s.trace(A2*T2**2),third=s.trace(A2*T2**3),
           projection_trace=s.trace(A2*e2),p='X^3/12+X^2/4-X/3')

    # Distinct complex eigenvalues: no reality of the spectrum is needed.
    T3=s.Matrix([[Q(6,5),-Q(8,5)],[Q(4,5),Q(3,5)]])
    e3=s.diag(1,0)
    basic_contract(T3,e3,s.Integer(1),s.Integer(3))
    require(not equal(T3*T3.H,T3.H*T3),'complex-spectrum example nonnormal')
    require(equal(T3*T3-Q(9,5)*T3+2*s.eye(2),s.zeros(2)),'Cayley-Hamilton identity')
    for lam in T3.eigenvals():
        require(equal(lam*s.conjugate(lam),2),'each squared eigenvalue modulus is 2')
    p3=Q(9,20)*T3-T3*T3/4
    require(equal(p3,s.eye(2)/2),'p takes value one half on simple spectrum')
    weighted_check(T3,e3,s.eye(2),p3)
    record('distinct_complex_eigenvalues',T=T3,e=e3,
           eigenvalues='(9 +/- I sqrt(119))/10',p='9 X/20-X^2/4',
           projection_trace=s.trace(e3),polynomial_trace=s.trace(p3))

    # A genuinely nonconstant logarithmic interpolant, positive real eigenvalues.
    T4=s.Matrix([[Q(48,25),-Q(14,25)],[Q(7,25),Q(24,25)]])
    basic_contract(T4,e3,s.Integer(1),s.Integer(3))
    require(not equal(T4*T4.H,T4.H*T4),'real-spectrum example nonnormal')
    eigenvalues=[(36+s.sqrt(46))/25,(36-s.sqrt(46))/25]
    require(equal(eigenvalues[0]*eigenvalues[1],2),'eigenvalue product exactly 2')
    z=s.Symbol('X')
    nodes=[(s.Integer(0),s.Integer(0))]+[(lam,s.log(lam**2)/s.log(4)) for lam in eigenvalues]
    p=s.interpolate(nodes,z).expand()
    coefficients=[p.coeff(z,k) for k in range(3)]
    p4=coefficients[0]*s.eye(2)+coefficients[1]*T4+coefficients[2]*T4**2
    residual=s.N(s.trace(p4)-1,80)
    require(abs(complex(residual))<1e-65,'80-digit nonlinear logarithmic trace check')
    require(equal(coefficients[0],0),'zero constant coefficient')
    record('nonconstant_logarithmic_values_numeric',T=T4,
           eigenvalues=[s.N(x,30) for x in eigenvalues],
           interpolation_values=[s.N(y,30) for x,y in nodes[1:]],
           trace_residual_80digits=residual,
           scope='The matrix identities are exact; logarithmic interpolation is a numerical regression.')

    # Shared constants matter in the two-system theorem.
    scalar=s.Matrix([[1]])
    zero=s.Matrix([[0]])
    one=s.Matrix([[1]])
    basic_contract(scalar,zero,s.Integer(1),s.Integer(3))
    basic_contract(scalar,one,Q(1,4),s.Integer(3))
    require(equal(scalar,scalar),'all positive moments coincide')
    require(s.trace(zero)!=s.trace(one),'different d permits different projection trace')
    record('counterexample_with_different_parameters',T=scalar,
           first_d=1,second_d=Q(1,4),shared_c=3,
           first_projection_trace=0,second_projection_trace=1)

    # The zero-dimensional case is vacuous and p=0 is permitted.
    E=s.zeros(0,0)
    require(E.det()==1,'empty determinant')
    require(s.trace(E)==0,'empty trace')
    record('zero_dimensional',determinant=E.det(),trace=s.trace(E),p='0')

    return {'status':'PASS','assertion_count':assertions,'case_count':len(cases),
            'sympy_version':s.__version__,
            'scope':'Exact finite algebra except one explicitly labelled 80-digit logarithmic interpolation check. These tests do not prove the universal theorem and do not compile Lean.',
            'cases':cases}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=main()
    payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(payload)
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
