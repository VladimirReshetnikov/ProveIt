#!/usr/bin/env python3
"""Independent exact SymPy verification of the Kerr-Newman family.

Coordinate order t,r,x,phi, with x=cos(theta).  Signature -+++.
No sampling, numerical approximation, or external CAS is used.
"""
import json
import time
from pathlib import Path
import sympy as sp

START = time.monotonic()
r, x, a, m, q = sp.symbols('r x a m q')
S = r*r+a*a*x*x
D = r*r-2*m*r+a*a+q*q
s = 1-x*x
B = r*r+a*a

def simp(z):
    return sp.cancel(z)

def der(z, i):
    return sp.diff(z, (r, x)[i-1]) if i in (1,2) else sp.S.Zero

def announce(msg):
    print(f'{time.monotonic()-START:8.2f}s {msg}', flush=True)

g = sp.zeros(4)
g[0,0] = (-D+a*a*s)/S
g[0,3] = g[3,0] = a*s*(D-B)/S
g[1,1] = S/D
g[2,2] = S/s
g[3,3] = s*(B*B-a*a*D*s)/S
gi = sp.zeros(4)
gi[0,0] = -(B*B-a*a*D*s)/(S*D)
gi[0,3] = gi[3,0] = a*(D-B)/(S*D)
gi[1,1] = D/S
gi[2,2] = s/S
gi[3,3] = (D-a*a*s)/(S*D*s)

checks = {}
def check(name, values):
    values = [simp(v) for v in values]
    failures = [(i, str(v)) for i,v in enumerate(values) if v != 0]
    checks[name] = {'count':len(values),'failures':failures}
    if failures: raise ValueError((name, failures))
    announce(f'{name}: {len(values)} exact zero residuals')

check('inverse', list(g*gi-sp.eye(4)))
check('determinant', [g.det()+S*S])

Gamma = [[[sp.S.Zero for k in range(4)] for j in range(4)] for i in range(4)]
for i in range(4):
    for j in range(4):
        for k in range(j,4):
            Gamma[i][j][k] = Gamma[i][k][j] = simp(sum(gi[i,l]*(der(g[l,k],j)+der(g[l,j],k)-der(g[j,k],l)) for l in range(4))/2)
announce('Christoffel symbols computed')
trace = [simp(sum(Gamma[k][i][k] for k in range(4))) for i in range(4)]
check('connection_trace', [trace[i]-der(S,i)/S for i in range(4)])
Ric = sp.zeros(4)
for i in range(4):
    for j in range(i,4):
        Ric[i,j] = Ric[j,i] = simp(sum(der(Gamma[k][i][j],k) + Gamma[k][i][j]*trace[k] for k in range(4))-der(trace[i],j)-sum(Gamma[k][i][l]*Gamma[l][j][k] for k in range(4) for l in range(4)))
        announce(f'Ricci {i}{j} computed')

# Compact rational-coframe formula.  e=(dt-a*s*dphi,dr,dx,B*dphi-a*dt).
C = sp.Matrix([[1,0,0,-a*s],[0,1,0,0],[0,0,1,0],[-a,0,0,B]])
Ric_expected = C.T*sp.diag(q*q*D/S**3,-q*q/(S*D),q*q/(S*s),q*q*s/S**3)*C
check('ricci_formula', list(Ric-Ric_expected))
check('scalar_curvature', [sum(gi[i,j]*Ric[i,j] for i in range(4) for j in range(4))])

A = sp.Matrix([-q*r/S,0,0,q*r*a*s/S])
F = sp.Matrix(4,4,lambda i,j:simp(der(A[j],i)-der(A[i],j)))
Fu = (gi*F*gi).applyfunc(simp)
Fd = (S*Fu).applyfunc(simp)
maxwell = [sum(der(Fd[i,j],i) for i in range(4)) for j in range(4)]
check('maxwell_divergence', maxwell)
check('bianchi_dF', [der(F[j,k],i)+der(F[k,i],j)+der(F[i,j],k) for i in range(4) for j in range(i+1,4) for k in range(j+1,4)])
F2 = simp(sum(F[i,j]*Fu[i,j] for i in range(4) for j in range(4)))
EM = (2*(F*gi*F.T-g*F2/4)).applyfunc(simp)
check('einstein_maxwell', list(Ric-EM))

output = {
  'conventions': {'coordinates':['t','r','x','phi'],'x':'cos(theta)','signature':'-+++','ricci':'d_k Gamma^k_ij - d_j Gamma^k_ik + Gamma^k_ij Gamma^l_kl - Gamma^k_il Gamma^l_jk','equation':'Ric_ij = 2(F_ir g^rs F_js - g_ij F_rs F^rs/4)'},
  'sympy_version':sp.__version__,
  'checks':checks,
  'metric':[[str(sp.factor(g[i,j])) for j in range(4)] for i in range(4)],
  'inverse':[[str(sp.factor(gi[i,j])) for j in range(4)] for i in range(4)],
  'ricci':[[str(sp.factor(Ric[i,j])) for j in range(4)] for i in range(4)],
  'maxwell_density':[[str(sp.factor(Fd[i,j])) for j in range(4)] for i in range(4)],
  'field':[[str(sp.factor(F[i,j])) for j in range(4)] for i in range(4)],
  'field_invariant':str(sp.factor(F2)),
  'seconds':round(time.monotonic()-START,3)
}
dest = Path(__file__).resolve().parents[1]/'certificates'/'sympy_results.json'
dest.write_text(json.dumps(output,indent=2)+'\n')
announce(f'PASS: wrote {dest.name}')
