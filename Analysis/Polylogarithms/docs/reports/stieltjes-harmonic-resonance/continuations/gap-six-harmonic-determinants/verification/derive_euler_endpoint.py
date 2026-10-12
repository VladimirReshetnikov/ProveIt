#!/usr/bin/env python3
"""Exact finite coefficient derivation of the classical Euler inputs.

This checks the algebra after the proved beta/gamma height-one identity and
convergent shuffle/stuffle laws. It is not an MZV relation search.
"""
import json
from pathlib import Path
import sympy as s

X,Y,P,z3,z5,z7=s.symbols("X Y pi_squared zeta3 zeta5 zeta7")
z={2:P/6,3:z3,4:P**2/90,5:z5,6:P**3/945,7:z7}
count=0

def check(expr):
    global count
    assert s.expand(expr)==0, expr
    count+=1

def truncate(expr):
    return s.Add(*(c*X**a*Y**b for (a,b),c in s.Poly(s.expand(expr),X,Y).terms()
                   if a+b<=7))

L=sum(z[k]*(X**k+Y**k-(X+Y)**k)/k for k in range(2,8))
height=truncate(-L-truncate(L**2)/2-truncate(L**3)/6)
def h(n,m):
    return s.expand(height).coeff(X,n-1).coeff(Y,m+1)

for n in range(2,8):
    check(h(n,0)-z[n])
for n in range(2,7):
    check(h(n,1)-s.Rational(n,2)*z[n+1]
          +sum(z[j+1]*z[n-j] for j in range(1,n-1))/2)

d32=3*z[2]*z[3]-s.Rational(11,2)*z[5]
d42=z[3]**2-s.Rational(4,3)*z[6]
d52=5*z[2]*z[5]+2*z[3]*z[4]-11*z[7]
check(2*d32+6*h(4,1)-z[5])
check(6*d42+12*h(5,1)-z[6])
d43=3*z[7]-2*z[3]*z[4]-10*h(6,1)-4*d52
check(3*d43+10*d52+20*h(6,1)-z[7])
check(2*(z[3]*z[4]-z[7]-d43)+3*d43+4*d52+10*h(6,1)-z[7])
T={n:s.expand(h(n,1)+z[n+1]) for n in [3,4]}
D={3:d32,4:d42,5:d52}
S={n:s.expand(2*h(n,2)+D[n]+2*h(n+1,1)+z[n+2]) for n in [3,4,5]}
check(T[3]-s.Rational(5,4)*z[4])
check(T[4]-3*z[5]+z[2]*z[3])
check(S[3]-s.Rational(7,2)*z[5]+z[2]*z[3])
check(S[4]-s.Rational(97,24)*z[6]+2*z[3]**2)
check(S[5]-6*z[7]+z[2]*z[5]+s.Rational(5,2)*z[3]*z[4])
endpoint=s.expand(-(S[3]+3*S[4]+2*S[5])/3+s.Rational(4,3)*(T[3]+2*T[4])
                  -1+s.Rational(13,12)*z[2]-s.Rational(31,12)*z[3])
expected=(-1+s.Rational(13,12)*z[2]-s.Rational(31,12)*z[3]
          +s.Rational(5,3)*z[4]+s.Rational(41,6)*z[5]
          -s.Rational(97,24)*z[6]-4*z[7]-s.Rational(7,3)*z[2]*z[3]
          +2*z[3]**2+s.Rational(2,3)*z[2]*z[5]
          +s.Rational(5,3)*z[3]*z[4])
check(endpoint-expected)
out=Path(__file__).resolve().parents[1]/"results"/"euler_derivation.json"
result={"exact_assertions":count,"Euler_T":{str(k):str(v) for k,v in T.items()},
        "Euler_S":{str(k):str(v) for k,v in S.items()},
        "endpoint":str(endpoint),
        "scope":"Finite algebra from the analytic height-one and shuffle/stuffle identities proved or stated in the article."}
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
