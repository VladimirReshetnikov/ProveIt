"""Exact finite beta/confluent controls and separate numerical diagnostics."""
from pathlib import Path
import json,math
import sympy as sp
import mpmath as mp
B=Path(__file__).resolve().parents[1];V=B/'verification'
t,z,u=sp.symbols('t z u');lam=sp.Symbol('lambda')
polynomials={m:sp.expand(sum(sp.binomial(m-2,j)*sp.rf(t+1,j)/sp.factorial(j+1)*z**j*(1-z)**(m-2-j) for j in range(m-1))) for m in range(2,11)}
assert polynomials[2]==1
assert sp.expand(polynomials[3]-(1+(t-1)*z/2))==0
assert sp.expand(polynomials[4]-((1-z)**2+(t+1)*z*(1-z)+(t+1)*(t+2)*z*z/6))==0
count=0
for m,P in polynomials.items():
    for n in range(13):
        # Coefficients of the closed expression (1-z)^(-t-m+1) P.
        actual=sum(co*sp.rf(t+m-1,n-j)/sp.factorial(n-j) for (j,),co in sp.Poly(P,z).terms() if j<=n)
        beta=sp.binomial(m+n-1,n)*sp.rf(1+t,n)/sp.factorial(n+1)
        assert sp.expand(actual-beta)==0
        count+=1
partial_fractions=0
for m in range(2,8):
    nodes=[sp.Rational(j+1,j+3) for j in range(m)]
    common=sp.prod(1-a*u for a in nodes)
    expression=sum(a**(m-1)*sp.prod(1-b*u for b in nodes if b!=a)/sp.prod(a-b for b in nodes if b!=a) for a in nodes)
    assert sp.expand(expression-1)==0
    partial_fractions+=1
q={1:-lam,**{2*j:sp.zeta(2*j)/j for j in range(1,5)}}
expa=[sp.Integer(1)]
for n in range(1,9):expa.append(sp.expand(sum(j*q.get(j,0)*expa[n-j] for j in range(1,n+1))/n))
assert sp.expand(24*expa[4]-(lam**4+2*sp.pi**2*lam**2+sp.Rational(7,15)*sp.pi**4))==0
assert sp.expand(polynomials[3]-(1+(t-1)*z/2)+sp.Rational(1,100))!=0

L2=sp.Symbol('L2',real=True)
A=sp.expand((lam**2+sp.pi**2/3)/(1-sp.I)).subs(lam,L2/2-sp.I*sp.pi/4).expand(complex=True)
assert sp.expand(sp.re(A)-(L2**2/8+13*sp.pi**2/96+sp.pi*L2/8))==0
assert sp.expand(sp.im(A)-(L2**2/8+13*sp.pi**2/96-sp.pi*L2/8))==0

mp.mp.dps=65
L=mp.log(2)/2-mp.j*mp.pi/4
def logistic(x):
    if x>=0:
        e=mp.exp(-x);return 1/(1+e),e/(1+e)**2
    e=mp.exp(x);return e/(1+e),e/(1+e)**2
def quadrature(fun):return mp.quad(fun,[-800,-100,-20,-5,0,5,20,100,800])
def evaluate(expr):return sp.lambdify(lam,expr,modules='mpmath')(L)
checks=[]
for m in [2,3,4]:
    P=sp.Poly(polynomials[m].subs(z,sp.I),t)
    for k in [0,1,2,4,6,8]:
        coefficient=sum(co*expa[k-j] for (j,),co in P.terms() if j<=k)
        target=math.factorial(k)*evaluate(coefficient)/(1-mp.j)**(m-1)
        def integrand(x):
            U,J=logistic(x);return x**k*J/(1-mp.j*U)**m
        value=quadrature(integrand);error=abs(value-target)
        assert error<mp.mpf('1e-55')
        checks.append(dict(kind='Gaussian-logarithmic-moment',m=m,k=k,absolute_residual=mp.nstr(error,12)))
for tau in [mp.mpf('-0.75'),mp.mpf('-0.25'),mp.mpf('0'),mp.mpf('0.25'),mp.mpf('0.5'),mp.mpf('0.75')]:
    for extra in [0,1]:
        def integrand(x):
            U,J=logistic(x);return mp.exp(tau*x)*J*U**extra/(1+U*U)
        value=quadrature(integrand)
        if not tau:target=mp.log(2)/2 if extra else mp.pi/4
        elif extra:target=mp.pi*(1-mp.power(2,-tau/2)*mp.cos(mp.pi*tau/4))/mp.sin(mp.pi*tau)
        else:target=mp.pi*mp.power(2,-tau/2)*mp.sin(mp.pi*tau/4)/mp.sin(mp.pi*tau)
        error=abs(value-target);assert error<mp.mpf('1e-55')
        checks.append(dict(kind='real-Gaussian-generator',t=str(tau),extra_power=extra,absolute_residual=mp.nstr(error,12)))
record=dict(status='PASS',exact_confluent_coefficient_identities=count,exact_partial_fraction_identities=partial_fractions,printed_base_polynomials=3,printed_quartic_moment=True,printed_real_second_moments=2,corruption_controls=1,numerical_diagnostics=dict(working_decimal_digits=65,interval_certified=False,logistic_coordinate_cutoff=800,cases=checks),scope='Finite exact algebra and independent logistic-coordinate quadrature; arbitrary-order identities have analytic proofs in the manuscript.')
(V/'logistic-resolvent-results.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='numerical_diagnostics'},indent=2))
print('Independent numerical diagnostics:',len(checks),'passed at 65 working digits.')
