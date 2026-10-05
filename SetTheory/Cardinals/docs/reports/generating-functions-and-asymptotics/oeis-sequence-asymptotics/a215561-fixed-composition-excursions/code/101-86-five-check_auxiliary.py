"""Exact root-pair elimination and second inverse-correction checks."""
from pathlib import Path
import json
import sympy as s
root=Path(__file__).resolve().parent
x1,x2,x3,x4,x5,E=s.symbols('x1 x2 x3 x4 x5 E')
P=-x1*E; Q=-1/(x5*E)
S=E*(x2+x1*x4*E)/(1-x1*x5*E**2); T=-x4/x5-S
F=(-x1**3*x5**3*E**6+x1**2*x5**2*(1-x3)*E**5
 +(x1**2*x5**2-x1*x2*x4*x5)*E**4
 +(2*x1*x3*x5-x1*x4**2-2*x1*x5-x2**2*x5)*E**3
 +(x1*x5-x2*x4)*E**2+(1-x3)*E-1)
if s.factor(P+Q+S*T-(x3-1)/x5-F/(x5*E*(1-x1*x5*E**2)**2))!=0:
    raise RuntimeError('root-pair elimination')

z,c,c1,L2=s.symbols('z c c1 L2',nonzero=True)
shift=-c1*z/(c-3*z)-L2*z*z/(c-3*z)
# z=1/nu0. Subtract the leading logarithmic value at nu0.
res=c*shift-3*s.log(1+z*shift)+c1*z/(1+z*shift)+L2*z*z/(1+z*shift)**2
if s.series(res,z,0,3).removeO().expand()!=0:
    raise RuntimeError('second inverse correction')
C1=13*(s.sqrt(5)-5)/50;C2=s.Rational(36,25)-63*s.sqrt(5)/125
L=s.simplify(C2-C1*C1/2)
if L!=(213-83*s.sqrt(5))/500:raise RuntimeError('log correction')
out={'passed':True,'root_pair_identity':True,'second_inverse_residual_order_at_least':3,'second_log_correction':str(L)}
(root/'auxiliary_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
