#!/usr/bin/env python3
"""Exact rational identities used in the proofs; requires SymPy."""
import json
from pathlib import Path
import sympy as s
u,m,x,X,Y,v,z,r,c=s.symbols('u m x X Y v z r c',real=True)
D=1+x*(u*u-(1+m)*u)
d=u*u-(1+m)*u
Q=X*Y*(X+Y)/((1+X*X)*(1+Y*Y))
checks={
 'G_m_kernel':s.diff((m-u)/D,m)-(1-x*u)/D**2,
 'variance_factor':d+m-(u-m)*(u-1),
 'variance_subtraction':d/D+m/(1-x*m)-(u-m)*(u-1)/(D*(1-x*m)),
 'fixed_weight_kernel_derivative':s.diff(Q,X)-Y*(2*X+Y*(1-X*X))/((1+X*X)**2*(1+Y*Y)),
 'compensated_geometric':z/(1-z)-z/(1-z*u)-z*z*(1-u)/((1-z)*(1-z*u)),
 'transport_geometric':z/(1-z*v)-z/(1-z*u*v)-z*z*v*(1-u)/((1-z*v)*(1-z*u*v)),
 'Euler_tail_derivative_sign':s.diff((1-v*v)**3/(1+v*v),v)+4*v*(1-v*v)**2*(2+v*v)/(1+v*v)**2,
}
# Last identity is N=3: derivative = -2v(1-v²)²[4+2v²]/(1+v²)².
result={name:s.cancel(expr)==0 for name,expr in checks.items()}
assert all(result.values()),result
root=Path(__file__).resolve().parents[1]
(root/'data/symbolic_checks.json').write_text(json.dumps({'sympy':s.__version__,'checks':result},indent=2)+'\n')
print('PASS:',len(result),'exact symbolic identities')
