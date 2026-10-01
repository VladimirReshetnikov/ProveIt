"""Expand the cubic and finite-field positivity identities exactly with SymPy."""
import sympy as s
a,b,h=s.symbols('a b h')
r=a+b;x=b/h;y=b*(b-1)/(h*(h+1))
J=a*(a-1)/2+a*x+y
A=(r-1)*(a+x)**2-2*r*(a-1)/a*J
B=(r-1)*x*(a+x)-r*(a*x+y)
C=b*(b*(r-1)*x*x-r*(b-1)*y)
F=a*(a*a+2*a*b-a-b)*h**3+a*(a*a+2*a*b-a+2*b*b-b)*h*h-b*(r-1)*(a*b-2*a-2*b)*h+a*b*b*(r-1)
assert s.cancel(A*a*h*h*(h+1)-F)==0
Q0=a*a*(b*b+2*b-1)+a*(b-1)*(2*b*b+3*b-1)+b*(b-1)**2
Q1=(r-1)*(2*a*b-a-b)
R0=a*(b*b+2*b-1)+(b-1)*(3*b-1)
R1=a*(3*b-1)+(b-1)
H=a*h*h-b*(r-1)
rhs=H*(Q0+Q1*h)+b*r*(r-1)*(R0+R1*h)
assert s.cancel((A*C-b*b*B*B)*a*h**3*(h+1)**2/(b*b*r)-rhs)==0
print('PASS: both symbolic identities over Q(a,b,h)')
