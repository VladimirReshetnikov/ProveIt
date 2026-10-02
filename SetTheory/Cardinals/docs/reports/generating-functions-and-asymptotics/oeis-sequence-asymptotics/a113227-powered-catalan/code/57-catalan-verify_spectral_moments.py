"""Independent high precision checks of exact positive spectral representation."""
import mpmath as m
m.mp.dps=110

def jy(t):
 z=2*m.sqrt(t)
 J=m.besselj(t,z);Y=m.bessely(t,z)
 a=J-m.sqrt(t)*m.besselj(t+1,z)
 b=m.sqrt(t)*m.bessely(t+1,z)-Y
 return J,Y,a,b

def H(t):
 _,_,a,b=jy(t)
 return m.cos(m.pi*t)*a+m.sin(m.pi*t)*b

def q(t):
 _,_,a,b=jy(t);return a/b

# Scan only low t; for k>=5 use the proven eventual pole equation near k.
roots=[]
last=m.mpf('0.0001');f=H(last)
for i in range(1,101):
 t=m.mpf(i)/20;g=H(t)
 if f*g<0:
  rt=m.findroot(H,(last,t),solver='anderson')
  if all(abs(rt-r)>m.mpf('1e-30') for r in roots):roots.append(rt)
 last=t;f=g
for k in range(5,65):
 k=m.mpf(k)
 # scaled displacement formulation avoids losing roots exponentially close to k
 q0=q(k)
 h=lambda d:m.tan(m.pi*d)+q(k+d)
 d=m.findroot(h,-q0/m.pi,solver='newton',tol=m.mpf('1e-100'),verify=False)
 roots.append(k+d)
weights=[]
for t in roots:
 _,_,a,b=jy(t);qt=a/b;dq=m.diff(q,t)
 weights.append(1/(t*b*b*(m.pi**2*(1+qt*qt)+m.pi*dq)))
print('First poles and weights')
for t,p in zip(roots[:8],weights[:8]):print(m.nstr(t,24),m.nstr(p,24))
assert abs(sum(weights)-1)<m.mpf('1e-50')
print('mass=',m.nstr(sum(weights),50))
p=[1];a=[1]
for n in range(1,31):
 p=[0]+[(p[k-1] if k-1<len(p) else 0)+k*sum(p[k:]) for k in range(1,n+1)]
 a.append(sum(p))
for n in [1,2,3,5,10,20,30]:
 sp=sum(p*t**n for t,p in zip(roots,weights))
 assert abs(sp/a[n]-1)<m.mpf('1e-35')
 print('moment',n,'exact',a[n],'relative_error',m.nstr(sp/a[n]-1,12))
print('weight asymptotics relative to Dobinski leading')
for i in [10,20,30,40,50]:
 k=round(float(roots[i]));p=weights[i]
 L=m.exp(-2)/m.sqrt(2*m.pi)*k**m.mpf('-1.5')*m.exp(k)/m.factorial(k)
 print(k,m.nstr(k*(p/L-1),18),'expected',m.mpf(11)/12)
