#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'GuardStrict87.lean').read_text()
for t in ('GuardGap87Draft.guard_of_zero','gap_of_87_zero','cast_C beta v hgap','(hX : q beta v*q beta v≤v 6)','C beta v*K<v 13','mul_lt_mul_left hb'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
count=0
for beta in range(1,6):
 for J in range(1,6):
  b=J*beta;q=1+b
  if q<3:continue
  F=1;alpha=q-2;C=q-F-alpha
  for K in range(5):
   X=q*q+(F-K-q*q)%b;N=C*(X+K*q)-F
   assert N%b==0;omega=N//b
   assert X>=q*q and F+alpha<q and omega>0 and (q-F-alpha)*(X+K*q)-F-b*omega==0
   assert C*K<omega;count+=1
assert count>0
for name in ('ordinary14-87-guard-gap-draft','ordinary14-86-to-87-positive-map-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'GuardStrict87.lean',D/'research/ordinary14-87-guard-gap-draft/GuardGap87.lean',D/'research/ordinary14-86-to-87-positive-map-draft/PositiveMap86To87.lean']
print(json.dumps({'scope':'source inventory, finite guard-only controls and draft receipt replays; no Lean invocation','finite_guard_controls':count,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
