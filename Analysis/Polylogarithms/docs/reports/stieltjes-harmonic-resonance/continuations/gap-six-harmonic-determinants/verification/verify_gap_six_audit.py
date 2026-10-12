#!/usr/bin/env python3
"""Independent exact source-matrix and constant checks for the gap-six audit."""
from pathlib import Path
import itertools
import json
import math
import sympy as s

def source_matrix(b):
    p,q=2*b-6,2*b
    def entry(i,k):
        j=b+i
        d=2*j+1
        h=d-p-q+2*k+1
        if h<0:
            return s.S.Zero
        total=s.S.Zero
        for upper,lower in [(d-q+1,p-2*k),(d-p+1,q-2*k)]:
            if 2<=lower<=upper:
                total+=s.binomial(upper,lower)/upper
        return s.bernoulli(h)*total
    return s.Matrix(b,b,entry)

def factors(n):
    a=math.prod(range(2*n-5,2*n+1)) if n>3 else 0
    b=math.prod(range(2*n-6,2*n))
    return a,b,2*(a+b)

nmax=13
R=[[s.S.Zero]*3 for _ in range(nmax+1)]
for j in range(3):
    R[j+1][j]=s.S.One
alpha=[s.S.Zero]+[2*abs(s.bernoulli(2*n))/s.factorial(2*n) for n in range(1,nmax)]
for n in range(4,nmax+1):
    a,b,d=factors(n)
    for j in range(3):
        R[n][j]=sum(alpha[n-k]*(b+factors(k)[0])*R[k][j] for k in range(1,n))/d
f=lambda b:s.Matrix(R[b+1:b+4]).det()

records=[]
for b in range(4,11):
    mat=source_matrix(b)
    minor=mat.minor_submatrix(b-1,0)
    assert minor==source_matrix(b-1)
    determinant=mat.det(method='domain-ge')
    inv=mat.inv()[0,b-1]
    assert inv==(-1)**(b-1)*minor.det(method='domain-ge')/determinant
    bridge=s.Rational((-1)**(b*(b-1)//2),4**b*math.factorial(b))*math.prod(factors(k)[2] for k in range(4,b+4))
    assert determinant==bridge*f(b)
    assert inv==4*b*f(b-1)/(factors(b+3)[2]*f(b))
    records.append({'b':b,'last_inverse_row_entry':str(inv),
                    'f_previous':str(f(b-1)),'f_current':str(f(b))})

N=s.Integer(4096)
b=s.Integer(2048)
V=s.Matrix(3,3,lambda i,j:s.Rational(1,(j+1)**(2*(i+1))))
permanent=sum(math.prod(V[i,perm[i]] for i in range(3)) for perm in itertools.permutations(range(3)))
margin=-V.det()-permanent*(s.Rational(26,25)**3-1)
assert V.det()==-s.Rational(5,1944)
assert permanent==s.Rational(289,23328)
assert margin==s.Rational(373661,364500000)>0
assert s.Rational(13,8)+s.Rational(8,15)==s.Rational(259,120)<s.Rational(9,4)
assert (N-5)**2-3600*(N+1)>0
assert 32*90<N-5
assert N**6<=2**(N-2)
assert (1+1/N)**6<2
assert 2**56*N**5*2**(-5*N)<s.Rational(1,4)
outer=s.Rational(1600,(2*b-2)**2)
middle=4/(2*b-1)+s.Rational(320,3*(2*b-2))
assert outer<s.Rational(1,25)
assert middle<s.Rational(1,25)
u=s.Rational(1,4)
quotient=((1-u)**(-3)-1-3*u)/u**2
assert quotient==s.Rational(268,27)<10

payload={
 'scope':'Independent audit of analytic constants and inverse-cofactor sign in gap_six_proof.tex',
 'sympy_version':s.__version__,
 'arithmetic':'Exact symbolic and rational/integer arithmetic; no floating point',
 'cofactor_checks':records,
 'auxiliary_f3':str(f(3)),
 'density_log_error_constant':str(s.Rational(259,120)),
 'binomial_remainder_quotient_at_quarter':str(quotient),
 'threshold_quadratic_value':str((N-5)**2-3600*(N+1)),
 'outer_relative_error_at_threshold':str(outer),
 'middle_relative_error_at_threshold':str(middle),
 'limiting_determinant':str(V.det()),'limiting_permanent':str(permanent),
 'determinant_margin':str(margin),
 'finite_sign_scope':'The full modular certificate proves nonvanishing, not positivity, for 4<=b<=2047. No positivity claim for 7<=b<=2047 follows from modular residues.',
 'results':'All checks passed. Analytic steps still require the written proofs, independently audited.'}
out=Path(__file__).resolve().parents[1]/'results'/'gap_six_audit_verification.json'
out.write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps({k:v for k,v in payload.items() if k!='cofactor_checks'},indent=2))
