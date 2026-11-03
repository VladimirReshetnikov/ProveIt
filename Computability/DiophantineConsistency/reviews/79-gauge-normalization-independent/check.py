from pathlib import Path
from hashlib import sha256
import json,re
root=Path('research/ten-positive-79-gauge-normalization');o=root/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='d557f2d79a82c19155aa048cf14ffaccec6e03ac34f3241069bb206d8f09c2ba';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='d73aa1f17c8f6608e0bbbf72ff7c71fb0827daac337b637bf7845691796a5f48'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().strip()=="'Mask79Gauge.preserve_rank_and_carrier' depends on axioms: [propext, Quot.sound]" and not (o/'stderr').read_text()
rows=json.loads(Path('research/ten-positive-79-mask-coordinate-probe/candidate.json').read_text())['source'];assert len(rows)==79
for k,v in {24:['G1','*','q','qmF'],25:['G','-','G1','C'],52:['V2','*','V','V'],55:['LBt','*','V2','Bt'],56:['center','-','n','LBt'],65:['mu2inner','*','mu2','Bt'],68:['Zpart2','*','Hp','brk'],69:['Znum','-','Zpart1','Zpart2']}.items():assert rows[k-1]==v
assert [i for i,r in enumerate(rows,1) if 'Bt' in r[2:]]==[55,65]
# Independently expand symbolic sparse integer polynomials, not just sample points.
class P:
 def __init__(self,x): self.d=x if isinstance(x,dict) else {():x}
 def __add__(self,b):
  if not isinstance(b,P):b=P(b)
  d=self.d.copy()
  for k,v in b.d.items():d[k]=d.get(k,0)+v
  return P({k:v for k,v in d.items() if v})
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,b):return self+-b if isinstance(b,P) else self+(-b)
 def __rsub__(self,b):return -self+b
 def __mul__(self,b):
  if not isinstance(b,P):b=P(b)
  d={}
  for a,x in self.d.items():
   for c,y in b.d.items():
    k=tuple(sorted(a+c));d[k]=d.get(k,0)+x*y
  return P({k:v for k,v in d.items() if v})
 __rmul__=__mul__
 def __eq__(self,b):return not (self-b).d
q,k,w,F,C,n,v,d,h,u,A,e=(P({(x,):1}) for x in 'q k w F C n v d h u A e'.split())

D=q*(k+w)+1
G=q*(q-F)-C;B=(k+w)*C-F
Gp=q*(q-(F+d))-(C-q*d);Bp=(k+w)*(C-q*d)-(F+d);np=n-v*D*d
assert Gp==G and Bp==B-D*d and np-v*Bp==n-v*B
# A abstracts the unchanged part of row 64; row 68 is Hp*(mu2*B+bJ*e).
Z=A-h*(u*B+e);Zp=A-h*(u*Bp+e)
assert Zp-Z==h*u*D*d
# Positive-integer guard equivalence after q*d<C, with d nonnegative.
for qq in range(1,6):
 for ff in range(1,6):
  for cc in range(1,15):
   for dd in range(6):
    if qq*dd<cc:assert (ff+dd+cc-qq*dd<qq)==(ff+cc<qq+(qq-1)*dd)
assert 1+1>=2 and all(1-2*dd<=0 for dd in range(1,20))
print('PASS: sparse integer-polynomial expansion verifies both all-ring identities and the row69 change; exact candidate row structure and counterexample/guard arithmetic checked.')
print('The checked Lean theorem is only ring algebra; normalization existence, graph preservation, unrestricted iff and producer/package ancestry remain unproved.')
