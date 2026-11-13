#!/usr/bin/env python3
"""Independent parent scaled-norm source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary13-parent-scaled-norms-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ParentScaledNorms.lean','fd89f72fd62079b4114f269dde9ab08d8ee2f997bfdc3503190766bec255311a').decode()
pin(A/'check_source.py','245c1c9bcdee7e6c34546665f1142ea973fe1c6df0f0938958d94a4ed10b1d28')
receipt=pin(A/'observation.json','3e708b40e4232cb0c48fd90ec4f27a1bea92fa4376e9e4ee7e9fe70eeb4efd66')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary13-parent-scaled-norms-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='a8af06b5bb1e3bf7dc0f0f7aee8a937a01907524751a012bce7b1100c9c329cd'
pin(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveScaledNorms2011.lean','b3b164e528edf0c2b51eecd994140d30389d80b36ae830dccc286dc0e6bf0863')
pin(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorMagnitude2011.lean','5fbf0c5c27f5172dfda4b9684629a44378b22872a48a2a718f1542701e236d49')
pin(D/'research/ordinary13-freej88-four-square-lean-draft/P88FourSquareGraph.lean','614cb3ed5a91e919b5e44a5ae7f4fa7210a0a8b41bf5953d99d54c303b4f042e')
for f in ('((factors p).1).evalRing v=1+(P88FourSquare.graph p).A0.evalRing v',
 '((factors p).2.1).evalRing v=1+(P88FourSquare.graph p).A1.evalRing v',
 '(hz : InternalZero (P88FourSquare.graph (fun j => (p j : ℤ))).output v) : ScaledNorms p v',
 '(FreeJ13.unit_iff_one _ _).mpr','unit_square_norm _ _ v hu0','unit_square_norm _ _ v hu1',
 'first_rhs_pair p v','main_rhs_pair p v'):
 assert f in s,f
# Exact free-ring polynomial comparison of the folded and adaptive carriers.
def plus(a,b):
 c=a.copy()
 for k,v in b.items():c[k]=c.get(k,0)+v
 return {k:v for k,v in c.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
 c={}
 for x,u in a.items():
  for y,v in b.items():
   z=tuple(i+j for i,j in zip(x,y));c[z]=c.get(z,0)+u*v
 return {k:v for k,v in c.items() if v}
one={(0,)*7:1};q,b,P,r0,k,Bt,Y=({tuple(int(i==j) for i in range(7)):1} for j in range(7))
M=mul(q,b)
folded=plus(plus(mul(M,plus(plus(P,r0),neg(mul(k,Bt)))),mul(Y,b)),neg(mul(q,Bt)))
adaptive=plus(plus(mul(M,plus(P,r0)),mul(Y,b)),neg(mul(mul(q,plus(one,mul(k,b))),Bt)))
assert folded==adaptive
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'same-valuation parent scaled-norm source review; no Lean','exact_folded_polynomial_identity':True},sort_keys=True,indent=2))
