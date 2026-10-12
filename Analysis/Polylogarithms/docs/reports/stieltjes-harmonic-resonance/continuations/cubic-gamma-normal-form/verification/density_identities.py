import sympy as s
v,n=s.symbols('v n');h=(1+3*v*v)/24;k=(v+v**3)/48;P2=(1-v*v)**2;P3=(1-v*v)**3

def gauge(f,a,q,order):
 for _ in range(order):f=s.diff(f,v)+a*s.diff(q,v)*f/q
 return s.cancel(f)
# Pure-u2 identity after division by h^(n-3).
a=n-3
pure=4*gauge(P2*h**2,a,h,2)-(192*h**3-(n+1)*P2*h+(2*n-1)*gauge(v*P2*h,a,h,1)-n*(n-2)*v*v*P2/4)
print('pure-u2 polynomial identity',s.factor(pure))
# Cubic-background identity after division by k^(n-4).
a=n-4
cubic=-8*gauge(P3*k**3,a,k,3)-((1-n)*P3*k*k+(1+3*n)*gauge(v*P3*k*k,a,k,1)+4*(1-3*n)*gauge(h*P3*k*k,a,k,2)-2*n*(5-3*n)*gauge(h*h*P3*k,a,k,1)+s.Rational(3,2)*n*(1-n)*v*h*P3*k+n*(n-1)*(3-n)*h**3*P3+9216*k**4)
print('all-n cubic density identity',s.factor(cubic))
base2=-8*s.diff(P3*k,v,3)-(-P3+7*s.diff(v*P3,v)-20*s.diff(h*P3,v,2)-96*P2*h+9216*k*k)
print('n=2 cubic density identity',s.factor(base2))
base1=s.diff(P3,v,3)/1152-(-s.diff(P2,v)/48-k)
print('n=1 cubic density identity',s.factor(base1))
