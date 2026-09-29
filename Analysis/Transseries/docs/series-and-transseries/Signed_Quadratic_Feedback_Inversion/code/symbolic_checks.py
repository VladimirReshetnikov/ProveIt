#!/usr/bin/env python3
"""Symbolic identities used by the two saddle calculations and the core jet."""
import json
from pathlib import Path
import sympy as s
n,r,a,R=s.symbols('n r a R',positive=True)
D=2*r*r+4*r+1
rp=r*(1+r)/(n*D)
f=n*r*(1+2*r)/(1+r)
def total(e): return s.diff(e,n)+s.diff(e,r)*rp
checks={}
checks['envelope_derivative']=s.simplify(total(f)-2*r)==0
h2=total(2*r-s.log(n))
checks['borel_second_derivative']=s.simplify(h2+(2*r+1)/(n*D))==0
checks['borel_stationary_value']=s.simplify((f+n-2*r*n).subs(n,r*(1+r)*s.exp(2*r)/a)-r*s.exp(2*r)/a)==0
j,k=s.symbols('j k',positive=True)
z=s.symbols('z',positive=True)
ff=(n-z)*(1+s.log(a*z*z/(n-z)))
checks['action_second_derivative']=s.simplify(s.diff(ff,z,2).subs({z:n/(1+r)})+D*(1+r)/(n*r))==0
t,L1,L2,w2,w3=s.symbols('t L1 L2 w2 w3')
c=L1+w2
q3=L1*L1/2+3*L1*w2+2*w2*w2-w2*L2-w3
Q=t-c*t*t+q3*t**3
H=Q*(1+L1*t+L1*L1*t*t/2)+w2*Q**2*(1+L2*t)+w3*Q**3
checks['core_cubic_jet']=s.series(H-t,t,0,4).removeO().expand()==0
checks['core_logarithmic_jet']=s.simplify(q3-c*c/2-(2*L1*w2+s.Rational(3,2)*w2*w2-w2*L2-w3))==0
assert all(checks.values()),checks
p=Path(__file__).resolve().parents[1]/'data'/'symbolic_checks.json'
# ed. (2026-09-29): newline='\n' keeps LF on Windows (no final newline, as delivered)
p.write_text(json.dumps(checks,indent=2),newline='\n')
print(json.dumps(checks,indent=2))
