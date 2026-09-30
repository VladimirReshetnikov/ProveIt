"""Optional exact symbolic cross-checks; requires SymPy."""
import json
from pathlib import Path
import sympy as s
from arithmetic import keller
x,y,z,t,A,B,C,a,r,b = s.symbols('x y z t A B C a r b')
F = s.Matrix(keller(x,y,z))
assert s.factor(F.jacobian([x,y,z]).det()) == -2
P,Q,R = F
u = y+1/x
assert s.factor(R*u**3-2*u*u+Q*u-2*P) == 0
assert s.factor(3*R*u*u-4*u+Q-2/x) == 0
D = 3*a*a-4*a+B*C
Atarget = a*(a*a-2*a+B*C)/(2*C*C)
point = (2*C/D,(2*a-D)/(2*C),D*(10*D-12*a-D*D)/(8*C*C))
for left,right in zip(keller(*point),(Atarget,B,C)):
    assert s.factor(left-right) == 0
f = t**3-t*t+b*t-(r**3-r*r+b*r)
q = t*t+(r-1)*t+r*r-r+b
assert s.expand(f-(t-r)*q) == 0
assert s.expand((3*r-1)**2-4*(3*r*r-2*r+b)-(-3*r*r+2*r+1-4*b)) == 0
assert s.rem(27*(r**3-r*r+r*b)-1-(3*r-1)**3,3*b-1,b) == 0
res = {'status':'PASS','sympy_version':s.__version__,
       'identities':['Jacobian determinant','inverse cubic','inverse derivative',
                     'three reconstruction coordinates','quadratic factor',
                     'quadratic discriminant','coefficient-gcd reduction']}
Path(__file__).resolve().parents[1].joinpath('data/symbolic.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))
