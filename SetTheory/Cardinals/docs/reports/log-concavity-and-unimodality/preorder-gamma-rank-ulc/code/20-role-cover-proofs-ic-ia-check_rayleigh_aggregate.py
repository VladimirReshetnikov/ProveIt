"""Exact arbitrary-class verification using formal first/second moments.
No bounded class enumeration or producer algebra is imported.
"""
import sympy as s
x,y,A,B,U,V,r,t=s.symbols('x y A B U V r t')

def delta(P,Q,L,M,correction):
 H=s.expand(P*Q-L*M+1+correction)
 return s.expand(s.diff(H,x)*s.diff(H,y)-H*s.diff(H,x,y))
checks={}
Q=t*B+(B*B-V)/2
checks['same_distinguished']=(2*delta(x*y+A*(x+y)+(A*A-U)/2,Q,x+y+A,t+B,x*t),(Q*A-B)**2+Q**2*U+V)
Q=(B*B-t*t-V)/2
checks['same_ordinary']=(2*delta(x*y+A*(x+y)+(A*A-r*r-U)/2,Q,x+y+A,B,r*t),(Q*A-B)**2+(Q*r-t)**2+Q**2*U+V)
checks['cross_distinguished']=(2*delta(x*A+(A*A-U)/2,y*B+(B*B-V)/2,x+A,y+B,x*y),A*A*V+B*B*U)
checks['cross_one_distinguished']=(4*delta(x*A+(A*A-U)/2,y*B+(B*B-t*t-V)/2,x+A,y+B,x*t),(A*(B+t)-2)**2+A*A*V+U*((B-t)**2+V))
checks['cross_ordinary']=(4*delta(x*A+(A*A-r*r-U)/2,y*B+(B*B-t*t-V)/2,x+A,y+B,r*t),(A*B-r*t-2)**2+(A*t-r*B)**2+U*(B*B+t*t)+V*(A*A+r*r)+U*V)
for name,(lhs,rhs) in checks.items():
 assert s.Poly(s.expand(lhs-rhs),x,y,A,B,U,V,r,t).is_zero,name
 print('PASS exact formal-moment identity',name)
print('PASS all five identities for arbitrary class counts, via e2=(sum^2-sum_squares)/2')
