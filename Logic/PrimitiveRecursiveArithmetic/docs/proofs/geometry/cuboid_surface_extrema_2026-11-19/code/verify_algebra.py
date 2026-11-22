#!/usr/bin/env python3
"""Exact symbolic checks of algebraic identities used in the proof.

SymPy is required. These checks certify the displayed rational identities;
the geometric arguments and the inequality sign hypotheses remain in the
human-readable proof. They do not constitute a Lean proof.
"""
import json
from pathlib import Path
import sympy as s

a,b,c,x,y,u,v=s.symbols("a b c x y u v", positive=True)
q0=(a+b)**2+c*c
q1=(b*b+c*c)*(a*a+2*a*c+2*c*c)/(2*c*c)
delta=a*(c-b)/(2*c)
A=(x+c)**2+y*y
B=x*x+(y+c)**2
C=(a+c-x)**2+(a+y)**2
D=(b+x)**2+(b+c-y)**2
checks={
 "vertex_transition_factor":q1-q0-a*(c-b)*(2*c*c-2*b*c-a*c-a*b)/(2*c*c),
 "W_radius_A":A.subs({x:a-delta,y:b-delta})-q1,
 "W_radius_C":C.subs({x:a-delta,y:b-delta})-q1,
 "W_radius_D":D.subs({x:a-delta,y:b-delta})-q1,
 "A_B_bisector":A-B-2*c*(x-y),
 "D_C_bisector":D-C-2*(a+b+c)*(x-y+b-a),
 "extra_E":(x-2*a-c)**2+y*y-C-2*a*((a-x)+(b-y)+(c-b)),
 "extra_F":x*x+(y-2*b-c)**2-D-2*b*((a-x)+(b-y)+(c-a)),
 "extra_P":(x-2*a-b)**2+(y-b-c)**2-D-4*(a+b)*(a-x),
 "extra_Q":(x-a-c)**2+(y-a-2*b)**2-C-4*(a+b)*(b-y),
 "extra_R":(x-a-b)**2+(y-a-b-c)**2-D-2*(a*(c-b)+(a+2*b)*(a-x)+a*(b-y)),
 "extra_S":(x-a-b-c)**2+(y-a-b)**2-C-2*(b*(c-a)+b*(a-x)+(2*a+b)*(b-y)),
 "diameter_sum_factor":(c+x+y)**2+(a+b-x-y)**2-q0-2*(x+y)*(x+y+c-a-b),
}
hv=v*v+2*c*v+a*a-b*b+2*c*(a-b)-2*a*b
v0=b-a*(c-b)/(b+c)
ku=u*u+2*c*u+b*b-a*a+2*c*(b-a)-2*a*b
u0=a-b*(c-a)/(a+c)
checks.update({
 "H_v0_positive":hv.subs(v,v0)-2*a*a*(b*b+c*c)/(b+c)**2,
 "K_u0_positive":ku.subs(u,u0)-2*b*b*(a*a+c*c)/(a+c)**2,
 "K_zero":ku.subs(u,0)-(a*a+b*b-2*(a+c)*u0),
 "d4_slack":(a+b)**2+(c+b-v)**2-((a+c)**2+v*v)-2*((b+c)*(b-v)-a*(c-b)),
 "d5_slack":(a+b)**2+(c+a-u)**2-((b+c)**2+u*u)-2*((a+c)*(a-u)-b*(c-a)),
})
results={name:s.factor(expr)==0 for name,expr in checks.items()}
if not all(results.values()):
    raise AssertionError([name for name,ok in results.items() if not ok])
out={"status":"passed","identities":results,"count":len(results),"sympy_version":s.__version__}
path=Path(__file__).resolve().parents[1]/"verification"/"symbolic_checks.json"
path.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
