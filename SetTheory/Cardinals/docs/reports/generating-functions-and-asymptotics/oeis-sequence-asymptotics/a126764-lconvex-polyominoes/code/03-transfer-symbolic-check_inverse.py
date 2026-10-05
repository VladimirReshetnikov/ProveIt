"""Exact-symbolic checks of L-convex coefficient and inverse expansions.
Run: python check_inverse.py
No external packages beyond SymPy.
"""
import json
from pathlib import Path
import sympy as s
K = s.symbols('K', positive=True)
u, v, T = s.symbols('u v T')
d = list(map(s.Rational, ['1','-1/6','-35/72','755/1296','-29375/31104','1772639/933120','-31514551/6718464','3808743271/282175488','-85931514901/1934917632']))
b=[]
for r in range(len(d)):
    b.append(s.expand(sum(d[j]*(2*K)**j*(-1)**(r-j)*s.factorial(r+2)/(s.factorial(r-j)*s.factorial(2*j+2-r)*2**(r-j)) for j in range(max(0,(r-1)//2),r+1))))
# Log coefficients by formal differentiation, B' = (log B)' B.
lam=[s.Integer(0)]
for r in range(1,len(d)):
    lam.append(s.expand(b[r]-sum(k*lam[k]*b[r-k] for k in range(1,r))/r))

# An independent Gaussian-saddle computation through z^-4.
# Set t=(2K/z)(1+i v/sqrt(z)), and w=z^-1/2.
R=4
w=s.symbols('w')
# Exponent is z-v²/2 + sum_{m>=1} (-i)^(m+2) v^(m+2) w^m /2.
g=[s.Integer(0)]+[(-s.I)**(m+2)*v**(m+2)/2 for m in range(1,2*R+1)]
e=[s.Integer(1)]
for m in range(1,2*R+1):
    e.append(s.expand(sum(k*g[k]*e[m-k] for k in range(1,m+1))/m))
amp=[]
for m in range(2*R+1):
    amp.append(s.expand(sum(d[j]*(2*K)**j*s.binomial(s.Rational(3,2)+j,m-2*j)*(s.I*v)**(m-2*j) for j in range(m//2+1))))
def normal_expectation(p):
    result=0
    for (degree,),coef in s.Poly(s.expand(p),v).terms():
        if degree%2 == 0:
            result+=coef*(s.factorial2(degree-1) if degree else 1)
    return s.expand(result)
saddle=[]
for m in range(2*R+1):
    integrated=normal_expectation(sum(amp[k]*e[m-k] for k in range(m+1)))
    if m%2:
        if integrated != 0: raise ArithmeticError('Odd Gaussian term did not vanish')
    else:
        saddle.append(integrated)
        if s.expand(integrated-b[m//2]) != 0: raise ArithmeticError('Gaussian and Bessel coefficients differ')

# General inverse: Y=log y; T=3log Y-log A; z=Y+T+sum P_r(T)/Y^r.
ls=s.symbols('l1:5')
P={}
correction=T
for r in range(1,5):
    residual=correction-T-3*s.log(1+u*correction)+sum(ls[j-1]*u**j*(1+u*correction)**(-j) for j in range(1,r+1))
    pr=-s.expand(s.series(residual,u,0,r+1).removeO()).coeff(u,r)
    P[r]=s.expand(pr)
    correction+=P[r]*u**r
residual=correction-T-3*s.log(1+u*correction)+sum(ls[j-1]*u**j*(1+u*correction)**(-j) for j in range(1,5))
if s.expand(s.series(residual,u,0,5).removeO()) != 0: raise ArithmeticError('Formal inversion failed')
squared=s.expand(s.series((1+u*correction)**2,u,0,6).removeO()/u**2)
N={r:s.collect(squared.coeff(u,r),T) for r in range(-2,4)}
# Lambert leading inverse: z0 solves Y=z0-3log z0+log A.
Q={}
correction_w=s.Integer(0)
for r in range(1,5):
    residual=correction_w-3*s.log(1+u*correction_w)+sum(ls[j-1]*u**j*(1+u*correction_w)**(-j) for j in range(1,r+1))
    qr=-s.expand(s.series(residual,u,0,r+1).removeO()).coeff(u,r)
    Q[r]=s.expand(qr)
    correction_w+=Q[r]*u**r

output={
    'd':[str(p) for p in d],
    'b_in_K':[str(p) for p in b],
    'lambda_in_K':[str(p) for p in lam[1:]],
    'P_inverse_z':{str(r):str(s.collect(p,T)) for r,p in P.items()},
    'N_inverse_n':{str(r):str(p) for r,p in N.items()},
    'Q_lambert_z':{str(r):str(p) for r,p in Q.items()},
    'checks':{'gaussian_saddle_orders':R,'reversion_orders':4,'passed':True}
}
Path(__file__).with_name('symbolic_results.json').write_text(json.dumps(output,indent=2)+'\n')
print('Independent Gaussian-saddle coefficients agree through z^-4.')
print('Formal inverse substitution agrees through Y^-4.')
for r in range(5): print('b_%d = %s'%(r,s.factor(b[r])))
for r in range(1,5):print('lambda_%d = %s'%(r,s.factor(lam[r])))
for r in range(1,5):print('P_%d = %s'%(r,s.collect(P[r],T)))
for r in range(-2,4):print('n coefficient Y^%d = %s'%(-r,N[r]))
for r in range(1,5):print('Q_%d = %s'%(r,Q[r]))
print('Numerical constants: K=%.15g, delta=%.15g, A=%.15g'%(float(13*s.pi**2/24),float(13*s.sqrt(2)/768),float(169*s.sqrt(39)*s.pi**3/13824)))
