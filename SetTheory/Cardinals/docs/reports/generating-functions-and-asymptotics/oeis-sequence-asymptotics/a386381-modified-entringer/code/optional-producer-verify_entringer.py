import math,json,sys
from pathlib import Path
from fractions import Fraction as Q
import mpmath as mp
import sympy as s
OUT=Path(__file__).parent
mp.mp.dps=110
rho=mp.pi/2
# Euler zigzag coefficients via classical Riccati relation, exact rational.
M=420
e=[Q(1)]
for n in range(M):
    e.append((sum(e[j]*e[n-j] for j in range(n+1))+(n==0))/(2*(n+1)))
p=[Q(1)]
for n in range(M):
    p.append(sum(e[j]*p[n-j] for j in range(n+1))/((n+1)**2))
# Frobenius H solution in t=1-z/rho, normalized H(0)=0, H'(0)=1.
h=[mp.mpf(0)]*(M+1)
for j in range(1,M,2):
    k=(j+1)//2
    h[j]=(-1)**k*2*mp.bernoulli(2*k)*rho**(2*k)/mp.factorial(2*k)
f=[mp.mpf(0),mp.mpf(1)]
for k in range(M-1):
    f.append((((k+1)**2+2)*f[k+1]+sum(h[j]*f[k-j] for j in range(1,k+1)))/((k+2)*(k+1)))
def qmp(q): return mp.mpf(q.numerator)/q.denominator
def val(c,x): return mp.fsum(qmp(q)*x**k if isinstance(q,Q) else q*x**k for k,q in enumerate(c))
def der(c,x): return mp.fsum(k*(qmp(q) if isinstance(q,Q) else q)*x**(k-1) for k,q in enumerate(c) if k)
connections=[]
for zratio in [mp.mpf('0.4'),mp.mpf('0.5'),mp.mpf('0.6')]:
    z=rho*zratio;t=1-zratio
    A=val(p,z);Ap=der(p,z);H=val(f,t);Ht=der(f,t)
    # z*(A*Ht/rho + Ap*H) = A(rho), since z W is constant.
    C=z*(A*Ht/rho+Ap*H)
    connections.append((str(zratio),mp.nstr(C,100),mp.nstr(mp.pi*C,100)))
C=mp.mpf(connections[1][1]);oeisc=mp.pi*C
# Independently generate original integer triangle.
row=[1];a=[1]
for n in range(1,803):
    nxt=[0]*(n+1);nxt[1]=row[-1]
    for k in range(2,n+1):nxt[k]=nxt[k-1]+(n-2)*row[n-k]
    row=nxt;a.append(row[-1])
source=[1,1,1,2,8,56,640,10960,264640,8581760,360331520,19031302400,1235451750400,96722377139200,8988790940876800,978442125179648000,123324448870740377600,17820979140159760793600,2926936219425738642227200,542215853077506417192140800,112527512540808439576566169600]
if a[:len(source)] != source:
    raise RuntimeError('Official A386381 source-term mismatch')
# (N+1)^2*p[N+1] = [z^N]B.
for N in range(100):
    predicted=math.factorial(N)**2*(N+1)**2*p[N+1]
    if predicted.denominator != 1 or predicted.numerator != a[N+2]:
        raise RuntimeError(f'ODE/triangle disagreement at N={N}')
# L(t)=rho cot(rho*t/2)*H(t); compute fixed coefficients symbolically.
t,r=s.symbols('t r');R=12
hs=s.series(r*s.cot(r*t/2),t,0,R+1).removeO()
fs=[s.Integer(0),s.Integer(1)]
for k in range(R):
    acc=sum(hs.coeff(t,j)*fs[k-j] for j in range(1,k+1))
    fs.append(s.simplify((((k+1)**2+2)*fs[k+1]+acc)/((k+2)*(k+1))))
Ls=s.series(hs*sum(c*t**j for j,c in enumerate(fs)),t,0,R+1).removeO()
L=[s.expand(Ls).coeff(t,j) for j in range(R+1)]
Lnum=[mp.mpf(str(x.subs(r,s.pi/2).evalf(112))) for x in L]
rows=[]
for N in [10,20,40,80,160,320,640,800]:
    ratio=mp.mpf(a[N+2])/(2*C*rho**(-N-1)*mp.factorial(N)**2)
    res={"N":N,"ratio":mp.nstr(ratio,40),"c_est_leading":mp.nstr(ratio*oeisc,35)}
    for K in [1,2,4,8,12]:
        appr=1+mp.fsum(Lnum[j]*(-1)**(j+1)*mp.factorial(j)/mp.fprod(N-i for i in range(j+1)) for j in range(K) if j<N)
        res['error_K'+str(K)]=mp.nstr(ratio-appr,25)
    rows.append(res)
# Pure inverse-N coefficients.
u=s.symbols('u')
expansion=1
for j in range(8):
    expansion+=L[j]*(-1)**(j+1)*s.factorial(j)*u**(j+1)/s.prod(1-i*u for i in range(j+1))
invseries=s.series(expansion,u,0,9)
result={"source_check":"All 21 terms printed on official A386381 matched", "ode_exact_check":"Original triangle versus ODE coefficient recurrence through original n=101", "dps":mp.mp.dps,"series_terms":M,"connection_values_diagnostic":connections,"L_coefficients":[str(x) for x in L],"inverse_N_series":str(invseries),"ratios":rows,"certificate_status":"Multiprecision diagnostics, not interval-enclosed values"}
(OUT/'entringer_diagnostics.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
