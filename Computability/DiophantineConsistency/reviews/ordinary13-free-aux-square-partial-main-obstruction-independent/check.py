#!/usr/bin/env python3
import hashlib,json,math
from pathlib import Path
root=Path(__file__).resolve().parents[2]; here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
cand=json.loads((root/'research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json').read_text())
r={x[0]:x[1:] for x in cand['source']}
for k,v in {'g15':['*',4,'a'],'H':['+',3,'g15'],'g17':['*','a','a'],
 'Delta':['+','H','g17'],'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],
 'g63':['*','Delta','c2'],'g64':['+',1,'g63'],'g65':['*','g62','g64'],
 'A1':['-','g61','g65'],'F1':['+',1,'A1'],'P01':['*','F0','F1'],
 'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]}.items():assert r[k]==v,(k,r[k])
# Coefficients of 1+(A^2-1)(A^2+1)^2, low-degree first.
def add(x,y):return [((x[i] if i<len(x) else 0)+(y[i] if i<len(y) else 0)) for i in range(max(len(x),len(y)))]
def mul(x,y):
 z=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i+j]+=a*b
 return z
L=add([1],mul([-1,0,1],mul([1,0,1],[1,0,1])))
R=mul([0,0,1],[-1,0,1,0,1])
assert L==R==[0,0,-1,0,1,0,1]
# Mod 4 the actual discriminant a^2+4a+3 is 0 or 3; hence
# 1+Delta*c^2 is 0 or 1, and the main factor cannot equal -1.
cases=0
for a in range(4):
 for c in range(4):
  t=(1+(a*a+4*a+3)*c*c)%4;assert t in (0,1)
  for U in range(4):
   for d in range(4):
    assert (1+d*d-U*U*t)%4!=3;cases+=1
for A in range(2,1001):
 t=A**4+A*A-1; r0=A*A*t
 assert A**4<t<(A*A+1)**2
 assert math.isqrt(r0)**2!=r0
print(json.dumps({'candidate_graph_rows_verified':15,'polynomial_identity_coefficients':L,
 'mod4_factor_unit_cases':cases,'nonsquare_sanity_checks':999,
 'scope':'c=Delta+2 only','other_candidate_zeros_excluded':False,
 'lean_executed':False},indent=2,sort_keys=True))
