#!/usr/bin/env python3
"""Reproduce A122399 saddle coefficients and exact tests. Python + mpmath + sympy."""
import json, math
from pathlib import Path
import mpmath as mp
import sympy as S
OUT=Path(__file__).parent
mp.mp.dps=90
J=7
Y=mp.findroot(lambda y:mp.log(1+mp.exp(-y))-y/(1+mp.exp(y)),1.15)
X=mp.log(1+mp.exp(-Y)); B=2-Y+X; D=1/(X*Y); C=1/(Y*mp.sqrt(2*mp.pi*B))
x,y,p=S.symbols('x y p')
# U_j=[s^j] X(y(1+s))/X(y); logistic derivatives and p=x/y.
u=[S.Integer(1)]; deriv=-p
for j in range(1,2*J+3):
    u.append(S.expand((y**j*deriv/(S.factorial(j)*x)).subs(p,x/y)))
    deriv=S.expand(-p*(1-p)*S.diff(deriv,p))
# f=-log(1+s)-log(U).
ell=[S.Integer(0)]
for j in range(1,len(u)):
    ell.append(S.expand(u[j]-S.Rational(1,j)*sum(k*ell[k]*u[j-k] for k in range(1,j))))
f=[S.Integer(0)]+[S.expand(S.Rational((-1)**j,j)-ell[j]) for j in range(1,len(u))]
assert all(not v.atoms(S.Float) for v in f), 'Unexpected floating-point contamination'
assert f[1]==0 and S.simplify(f[2]-(2-y+x)/2)==0
fv=[mp.mpf(str(S.N(v.subs({x:str(X),y:str(Y)}),85))) for v in f]
# Sparse (half-power of n^-1, power of Gaussian variable) expansion.
P={(0,0):mp.mpf(1)}
for k in range(3,2*J+3):
    weight=k-2; Q={}
    for a in range(2*J//weight+1):
        e=fv[k]**a/mp.factorial(a)
        for (r,d),v in P.items():
            if r+a*weight<=2*J:
                key=(r+a*weight,d+a*k); Q[key]=Q.get(key,0)+v*e
    P=Q
raw=[]
for j in range(J+1):
    v=mp.mpf(0)
    for a in range(2*j+1):
        amp=(-1)**a*(a+1)
        for (r,d),q in P.items():
            if r+a==2*j:
                k=d+a
                assert k%2==0
                moment=(-1)**(k//2)*mp.factorial(k)/(mp.factorial(k//2)*2**(k//2)*B**(k//2))
                v+=amp*q*moment
    raw.append(v)
co=[raw[0]]+[raw[j]+raw[j-1] for j in range(1,J+1)]
# Formal log expansion.
logco=[mp.mpf(0)]
for j in range(1,J+1):
    logco.append(co[j]-sum(k*logco[k]*co[j-k] for k in range(1,j))/j)
# Stirling log correction: log a_n=2nlogn+(logD-2)n+.5logn+log(2pi C)+sum L_j n^-j
L=logco.copy()
for j in range(1,J+1):
    if j%2: L[j]+=2*mp.bernoulli(j+1)/(j*(j+1))
mu=1/Y; variance=(B-1)/(B*Y**2)
yp=1/B-1; bp=(B-1-X/Y)/B
mu0=-yp/Y-bp/(2*B)
constants={k:mp.nstr(v,75) for k,v in dict(x=X,y=Y,B=B,D=D,C=C,block_mean_slope=mu,block_variance_slope=variance,block_mean_constant=mu0).items()}
print(json.dumps(constants,indent=2))
print('coefficients',*[mp.nstr(v,65) for v in co],sep='\n')
print('log coefficients incl Stirling',*[mp.nstr(v,65) for v in L],sep='\n')
# Recurrence for k! S(n,k): T(n,k)=k*(T(n-1,k)+T(n-1,k-1)).
T=[1]; tests=[]
for n in range(1,801):
    T=[0]+[k*((T[k] if k<len(T) else 0)+T[k-1]) for k in range(1,n+1)]
    if n in [1,2,3,4,5,10,20,40,80,100,160,320,640,800]:
        terms=[T[k]*pow(k,n) for k in range(n+1)]
        an=sum(terms)
        leading=C*D**n*mp.factorial(n)**2/mp.sqrt(n)
        ratio=mp.mpf(an)/leading
        residuals=[ratio-sum(co[j]/mp.mpf(n)**j for j in range(order+1)) for order in range(J+1)]
        mean=mp.fsum(mp.mpf(k)*v for k,v in enumerate(terms))/an
        var=mp.fsum((mp.mpf(k)-mean)**2*v for k,v in enumerate(terms))/an
        if n>=40:
            for j in range(J):
                assert abs(residuals[j]*mp.mpf(n)**(j+1)-co[j+1])<mp.mpf(1)/n
            assert abs(mean-mu*n-mu0)<mp.mpf(1)/n
            assert abs(var-variance*n)<1
        tests.append({'n':n,'a_n':str(an) if n<=10 else None,'ratio':mp.nstr(ratio,70),'scaled_residuals':[mp.nstr(v*mp.mpf(n)**(j+1),40) for j,v in enumerate(residuals)],'mean_minus_slope':mp.nstr(mean-mu*n,45),'variance_minus_slope':mp.nstr(var-variance*n,45)})
print(json.dumps(tests,indent=2))
result={'constants':constants,'phase_coefficients':[str(v) for v in f], 'coefficients':[mp.nstr(v,80) for v in co],'log_coefficients_including_stirling':[mp.nstr(v,80) for v in L],'tests':tests}
(OUT/'numerical_results.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'phase_coefficients.txt').write_text('\n'.join(f'f_{j} = {v}' for j,v in enumerate(f))+'\n')
