#!/usr/bin/env python3
"""Independent symbolic checks; requires SymPy. Writes a readable report."""
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parents[1]
p,t,u,q=s.symbols('p t u q',real=True)
A,B,C=s.symbols('A B C',positive=True)
checks=[]
def zero(label, expression):
    value=s.simplify(expression)
    if value != 0:
        raise AssertionError((label,value))
    checks.append(label+': PASS')
f=[(1-p)**2-t*t,2*p*(1-p)+2*t*t,p*p-t*t]
F=sum(x*x for x in f)
D=1-6*p+6*p*p
zero('Order-two collision difference',F-F.subs(t,0)+2*D*t*t-6*t**4)
zero('Order-two center curvature',s.diff(1-F,t,2).subs(t,0)-4*D)
P=(A-t*t)**q+(B+2*t*t)**q+(C-t*t)**q
zero('All-order center curvature',s.diff(P,t,2).subs(t,0)+2*q*(A**(q-1)-2*B**(q-1)+C**(q-1)))
Pu=(A-u)**q+(B+2*u)**q+(C-u)**q
zero('Fourth-order coefficient',s.diff(P,t,4).subs(t,0)/24-
     q*(q-1)/2*(A**(q-2)+4*B**(q-2)+C**(q-2)))
C1=p*p+(1-p)**2
zero('Single-coin Renyi-2 concavity',s.diff(-s.log(C1),p,2)+8*p*(1-p)/C1**2)
a,b=s.symbols('a b',real=True)
C2=((1-a)*(1-b))**2+(a+b-2*a*b)**2+(a*b)**2
HT=1-C2
M=s.hessian(HT,(a,b)).subs({a:s.Rational(1,10),b:s.Rational(1,10)})
if M != s.Matrix([[-73,-96],[-96,-73]])/25:
    raise AssertionError(M)
checks.append('Exact Tsallis-2 Hessian at (1/10,1/10): '+str(M))
ss,rr=s.symbols('s r')
Q=1-2*ss+2*ss**2+(2-6*ss)*rr+6*rr**2
zero('Collision completed square',Q-(6*(rr-(3*ss-1)/6)**2+(5-6*ss+3*ss**2)/6))
report='SymPy version: '+s.__version__+'\n'+'\n'.join(checks)+'\n'
(ROOT/'results'/'symbolic_checks.txt').write_text(report)
print(report)
