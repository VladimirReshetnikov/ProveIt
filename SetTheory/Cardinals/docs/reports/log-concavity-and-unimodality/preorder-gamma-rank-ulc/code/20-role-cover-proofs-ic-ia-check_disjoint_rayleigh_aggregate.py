"""Independent symbolic verification of all seven arbitrary-class identities."""
import sympy as s
x,y,A,B,U,V,r,t,v,w=s.symbols('x y A B U V r t v w')
def delta(P,Q,L,M,K):
 H=s.expand(P*Q-L*M+1+K)
 return s.expand(s.diff(H,x)*s.diff(H,y)-H*s.diff(H,x,y))
checks={};M=v+w+B;Q=(M*M-v*v-w*w-V)/2
checks['same_both_distinguished']=(2*delta(x*y+A*(x+y)+(A*A-U)/2,Q,x+y+A,M,x*v+y*w),(Q*A-B)**2+Q**2*U+V)
checks['same_one_distinguished']=(2*delta(x*y+A*(x+y)+(A*A-t*t-U)/2,Q,x+y+A,M,x*v+t*w),(Q*A-(M-v))**2+(Q*t-w)**2+Q**2*U+V)
checks['same_ordinary']=(2*delta(x*y+A*(x+y)+(A*A-r*r-t*t-U)/2,Q,x+y+A,M,r*v+t*w),(Q*A-M)**2+(Q*r-v)**2+(Q*t-w)**2+Q**2*U+V)
checks['cross_partnered']=(2*delta(x*A+(A*A-t*t-U)/2,y*B+(B*B-w*w-V)/2,x+A,y+B,x*y+t*w),(A*w-B*t)**2+A*A*V+B*B*U)
checks['cross_unpartnered']=(4*delta(x*A+(A*A-t*t-U)/2,y*B+(B*B-v*v-V)/2,x+A,y+B,x*v+t*y),(A*B+t*B+v*A-t*v-2)**2+U*(B-v)**2+V*(A-t)**2+U*V)
checks['cross_one_distinguished']=(4*delta(x*A+(A*A-t*t-U)/2,y*B+(B*B-v*v-w*w-V)/2,x+A,y+B,x*v+t*w),(A*(B+v)-t*w-2)**2+(A*w-t*(B-v))**2+V*(A*A+t*t)+U*((B-v)**2+w*w)+U*V)
K=r*v+t*w
checks['cross_ordinary']=(4*delta(x*A+(A*A-r*r-t*t-U)/2,y*B+(B*B-v*v-w*w-V)/2,x+A,y+B,K),(A*B-K-2)**2+(A*v-B*r)**2+(A*w-B*t)**2+(r*w-t*v)**2+U*(B*B+v*v+w*w)+V*(A*A+r*r+t*t)+U*V)
for name,(lhs,rhs) in checks.items():
 assert s.Poly(s.expand(lhs-rhs),x,y,A,B,U,V,r,t,v,w).is_zero,name
 print('PASS exact formal-moment identity',name)
print('PASS all seven arbitrary-class identities')
