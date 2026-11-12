#!/usr/bin/env python3
"""Independent 87 own-zero first quotient source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-first-quotient-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'FirstQuotient87.lean','b86f9cc58c8f43c9810c8cf0b5ac52d41655433ee5fd1fd7605520af33cf0fbd').decode()
pin(A/'check_source.py','2a71637141029b8742cecfe06d1ff79659b31be1ba7112c5cea4dcddecf94073')
receipt=pin(A/'observation.json','08757529120aaef8855c5603e6cd592a66ab2fb79b0b8c4fdece2058eafab6fd')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-first-quotient-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='7df2cc9703b0820bbc6d9869f3078cef1aa700cc55edd909520be78c8dc67368'
for f in ('(P87ShiftedGuard.graph p).A0=(P86ResidueGraph.graph p).A0',
 '(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 '(eval (P87ShiftedGuard.graph p).aux v-1)',
 'fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive).1',
 '(hbeta : 0<beta) (hJ : 0<v 0) (hY : 0<v 7)',
 'first_eval p beta v hport','QCubeQuotientFactsDraft.quotient_and_root (b beta v) (v 7) (firstP v) (v 8)'):
 assert f in s,f
assert 'InternalZero (P86ResidueGraph.graph p).output' not in s
old=json.loads((D/'research/ordinary14-shifted-guard87-probe/candidate.json').read_bytes())
new=json.loads((D/'research/ordinary14-residue-guard86/candidate.json').read_bytes())
def reachable(g):
 rows={r[0]:r[1:] for r in g['source']};seen={};stack=['A0']
 while stack:
  key=stack.pop()
  if key not in rows or key in seen:continue
  op,x,y=rows[key];seen[key]=(op,x,y)
  stack.extend(z for z in (x,y) if isinstance(z,str))
 return seen
assert reachable(old)==reachable(new)
# Construct signed-square examples with each sign of the same scaled root.
n=0
for b in range(1,6):
 q=1+b;Q=q**3;M=Q*b
 for t in range(1,5):
  Y=Q*t
  for P in range(4,9):
   for tau in range(1,4):
    for sign in (-1,1):
     root=P+t-sign*tau
     if root<=0:continue
     z=M*P+b*Y-M*root
     assert z==sign*M*tau and z*z==M*M*tau*tau
     n+=1
assert n>0
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ('ordinary14-86-first-fields-draft-independent','ordinary14-85-86-quotient-facts-draft-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero source and first-quotient review only; no Lean',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'signed_first_field_controls':n},sort_keys=True,indent=2))
