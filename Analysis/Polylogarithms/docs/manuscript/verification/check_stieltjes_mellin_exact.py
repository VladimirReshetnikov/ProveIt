"""Finite exact coefficient audits; these complement the analytic proof."""
from pathlib import Path
import json
import sympy as S

u,v,y=S.symbols('u v y', real=True)
N=12
d=S.symbols(f'd0:{N+2}')
M=S.symbols(f'M0:{N+1}')
zeta={j:S.Symbol(f'Z{j}') for j in range(2,N+3)}
records=[]

# Derive from independent Laurent multiplication, retaining moment symbols.
laurent=d[0]/v+sum(M[j]*v**j/S.factorial(j) for j in range(N))
sine=sum((-1)**k*S.pi**(2*k)*v**(2*k+1)/S.factorial(2*k+1)
         for k in range(N//2+1))
product=S.expand(laurent*sine)
for n in range(1,N+1):
    extracted=S.factorial(n)*product.coeff(v,n)
    explicit=sum((-1)**k*S.factorial(n)*S.pi**(2*k)*M[n-2*k-1]
                 /(S.factorial(2*k+1)*S.factorial(n-2*k-1))
                 for k in range((n-1)//2+1))
    if n%2==0:
        explicit+=(-1)**(n//2)*S.pi**n*d[0]/(n+1)
    residual=S.expand(extracted-explicit)
    assert residual==0
    records.append(dict(kind='sine_reconstruction',n=n,residual=str(residual)))
    imaginary=S.expand(S.im((y+S.I*S.pi)**n)/S.pi)
    polynomial=sum((-1)**k*S.binomial(n,2*k+1)*S.pi**(2*k)*y**(n-2*k-1)
                   for k in range((n-1)//2+1))
    assert S.expand(imaginary-polynomial)==0
    records.append(dict(kind='kernel_polynomial',n=n,residual='0',polynomial=str(polynomial)))

# Derive raising coefficients by differentiating the Gamma-quotient log,
# rather than encoding the claimed digamma-series convolution directly.
R=sum((-1)**n*d[n]*u**n/S.factorial(n) for n in range(N+2))
logB=sum((-1)**j*zeta[j]*(v**j+(u-v)**j-u**j)/j for j in range(2,N+3))
endpoint=S.expand(S.diff(logB,v).subs(v,0)*R-S.diff(R,u))
for n in range(N+1):
    extracted=(-1)**n*S.factorial(n)*endpoint.coeff(u,n)
    explicit=d[n+1]+sum(S.factorial(n)/S.factorial(n-k)*zeta[k+1]*d[n-k]
                         for k in range(1,n+1))
    assert S.expand(extracted-explicit)==0
    records.append(dict(kind='raising_gamma_quotient',n=n,residual='0'))

# Adjacent shifts a=1,b=2 have d0=1, dn=0 for n>=1 and f(x)=1/(1+x).
# Its subtracted Mellin germ is pi*csc(pi*v)-1/v.  Check all logarithmic
# moments and endpoint corrections from this independent elementary model.
adjacent=S.series(S.pi/S.sin(S.pi*v)-1/v,v,0,N).removeO().expand()
for n in range(1,N+1):
    substitution={d[0]:1}
    substitution.update({M[j]:S.factorial(j)*adjacent.coeff(v,j) for j in range(N)})
    value=S.simplify(S.factorial(n)*product.coeff(v,n).subs(substitution))
    assert value==0
    records.append(dict(kind='adjacent_shift_elementary_control',n=n,residual='0'))

# Finite operator reconstruction, checked by repeated exact application of
# the triangular raising operator, independently of the formal ODE proof.
limit=8
inverse=[S.Integer(1),S.Integer(0)]
for n in range(2,limit+1):
    inverse.append(S.expand(-sum(zeta[k]*inverse[n-k] for k in range(2,n+1))/n))
powers=[d[0]]
for j in range(1,limit+1):
    previous=S.Poly(powers[-1],*d)
    value=S.Integer(0)
    for monomial,coefficient in previous.terms():
        if sum(monomial)!=1:
            raise AssertionError('Unexpected nonlinear operator expression')
        n=monomial.index(1)
        value+=coefficient*(d[n+1]+sum(S.factorial(n)/S.factorial(n-k)*zeta[k+1]*d[n-k]
                                      for k in range(1,n+1)))
    powers.append(S.expand(value))
for n in range(limit+1):
    recovered=S.factorial(n)*sum(inverse[n-j]*powers[j]/S.factorial(j) for j in range(n+1))
    assert S.expand(recovered-d[n])==0
    records.append(dict(kind='finite_operator_reconstruction',n=n,residual='0'))

# Test rejection of characteristic errors; nonzero exact residuals required.
controls={
    'omit_even_endpoint_correction':S.factorial(2)*product.coeff(v,2)-2*M[1],
    'reverse_sine_sign_at_cubic':S.factorial(3)*product.coeff(v,3)-(3*M[2]+S.pi**2*M[0]),
    'omit_raising_zeta_term':S.factorial(2)*endpoint.coeff(u,2)-d[3],
    'replace_factorial_ratio_by_binomial':
        S.factorial(3)*(-1)**3*endpoint.coeff(u,3)-
        (d[4]+sum(S.binomial(3,k)*zeta[k+1]*d[3-k] for k in range(1,4))),
}
assert all(S.expand(value)!=0 for value in controls.values())
out=dict(scope='Finite exact symbolic checks, not a substitute for endpoint and interchange proofs.',
         sympy_version=S.__version__,records=records,
         rejected_negative_controls={key:str(S.expand(value)) for key,value in controls.items()},
         all_passed=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(f'{len(records)} exact identities and {len(controls)} rejected controls passed.')
