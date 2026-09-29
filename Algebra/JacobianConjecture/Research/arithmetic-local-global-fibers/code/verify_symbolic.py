#!/usr/bin/env python3
"""Exact symbolic identity checks. Requires SymPy; no numerical tolerances."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s

x,y,z,w,t,A,B,C,n,v=s.symbols('x y z w t A B C n v')

def F(x,y,z):
    u=1+x*y
    h=u*u*z+y*y*(1+3*u)
    return s.Matrix([u*h,y+3*x*h,x*(5-3*u-x*x*z)])

checks=[]
def zero(expr,name):
    num=s.cancel(expr).as_numer_denom()[0]
    assert s.expand(num)==0,name
    checks.append(name)

f=F(x,y,z)
zero(f.jacobian([x,y,z]).det()+2,'formal Jacobian determinant = -2')
source=s.Matrix([1/w,t-w,5*w*w-3*t*w-C*w**3])
expected=s.Matrix([w*t+t*t-C*t**3,2*w+4*t-3*C*t*t,C])
for i,e in enumerate(F(*source)-expected):
    zero(e,f'finite-root chart: coordinate {i+1}')
g=C*t**3-2*t*t+B*t-2*A
d=s.diff(g,t)
zero((expected[1]-B).subs(w,d/2),'derivative reconstruction of B')
zero((expected[0]-A).subs(w,d/2)-g/2,'reconstruction of A modulo cubic')
zero(g.subs({A:f[0],B:f[1],C:f[2]}, simultaneous=True).subs(t,y+1/x),
     'inverse cubic on source')
zero(d.subs({B:f[1],C:f[2]}, simultaneous=True).subs(t,y+1/x)-2/x,
     'derivative identity d=2/x')
Delta=4*B**2-4*C*B**3-64*A+72*C*A*B-108*C**2*A**2
zero(s.discriminant(g,t)-Delta,'binary-cubic discriminant formula')

# Infinity chart (v=S/T).
k=1-B*v+3*A*v*v
ys=B-3*A*v
src=s.Matrix([v/k,ys,A*k**3-k*(k+3)*ys**2])
rs=2*v-B*v*v+2*A*v**3
for i,e in enumerate(F(*src)-s.Matrix([A,B,rs])):
    zero(e,f'infinity chart: coordinate {i+1}')
zero(1+src[0]*src[1]-1/k,'infinity chart u=1/k')

roots=(0,n,1-n)
ds=(-n*(n-1),n*(2*n-1),(n-1)*(2*n-1))
zero((2*t**3-2*t*t-2*n*(n-1)*t)-2*t*(t-n)*(t+n-1),
     'split-family inverse factorization')
for i,(root,D) in enumerate(zip(roots,ds)):
    point=(1/D,root-D,5*D**2-3*root*D-2*D**3)
    for j,e in enumerate(F(*point)-s.Matrix([0,-2*n*(n-1),2])):
        zero(e,f'family branch {i}: coordinate {j+1}')

# Universal coefficient/gcd identities used in all-prime proof.
zero((2*n-1)-2*n+1,'gcd(n,2n-1) certificate')
zero((2*n-1)-2*(n-1)-1,'gcd(n-1,2n-1) certificate')
# Characteristic-three reduction, component by component.
zero(f[1]-y-3*x*((1+x*y)**2*z+y*y*(4+3*x*y)),
     'second component = y modulo 3')
char3=s.Poly(s.expand(f[0]-(z+y*y-y**3*f[2])),x,y,z, modulus=3)
assert char3.is_zero
checks.append('first component = z+y^2-y^3 R modulo 3')

report={'sympy_version':s.__version__,'checks':checks,'status':'PASS'}
path=Path(__file__).resolve().parents[1]/'certificates'/'symbolic_checks.json'
path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(f'SymPy {s.__version__}: {len(checks)} exact symbolic checks PASS')
for name in checks:
    print('PASS:',name)
