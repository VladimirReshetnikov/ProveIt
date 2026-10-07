from pathlib import Path
import sympy as s
import mpmath as mp
import json
r,t,q=s.symbols('r t q')
M=10
ct=s.series(r*t*s.cot(r*t/2),t,0,2*M+2).removeO().expand()
h=[s.S(0),s.S(1)]
for m in range(1,M+1):
 h.append(s.expand(((m*m+2)*h[m]+sum(ct.coeff(t,2*j)*h[m-2*j] for j in range(1,m//2+1)))/(m*(m+1))))
L=[s.expand(sum(ct.coeff(t,k)*h[j+1-k] for k in range(j+2))) for j in range(M)]
series=s.series(1+sum(L[j]*(-1)**(j+1)*s.factorial(j)*q**(j+1)/s.prod(1-k*q for k in range(j+1)) for j in range(M)),q,0,7).removeO().expand()
print('L',L[:5]);print('b',[series.coeff(q,k) for k in range(7)])
mp.mp.dps=70; rho=mp.pi/2
N=400
e=[mp.mpf(1)]
# e_j is the scaled EGF coefficient e_j*rho^j
for k in range(N):e.append(rho*(sum(e[j]*e[k-j] for j in range(k+1))+(1 if k==0 else 0))/(2*(k+1)))
a=[mp.mpf(1)]
for k in range(1,N+2):a.append(rho*sum(e[j]*a[k-1-j] for j in range(k))/(k*k))
vals=[]
for n in [25,50,100,200,400]:
 approx=sum(mp.mpf(str(s.N(series.coeff(q,k).subs(r,rho),75)))*mp.mpf(n)**(-k) for k in range(7))
 A0=(n+1)**2*a[n+1]/(2*approx)
 vals.append({'N':n,'c_estimate':mp.nstr(mp.pi*A0,60)})
print(vals)
json.dump({'L':[str(x) for x in L], 'b':[str(series.coeff(q,k)) for k in range(7)],'diagnostics':vals},open(Path(__file__).with_name('checks.json'),'w'),indent=2)
