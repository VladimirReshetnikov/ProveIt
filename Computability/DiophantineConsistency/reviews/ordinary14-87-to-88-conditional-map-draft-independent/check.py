#!/usr/bin/env python3
"""Independent guard map source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-to-88-conditional-map-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','f61b54c8e99827b699abb8b6a8d5826d593872d49056c59de3ee7882c74eb40e')
s=pin(A/'ConditionalMap87To88.lean','119cc14a16e4ddef1fff1f9ef0118f682ea17cf2b519cd4c12a45083305f6b91').decode()
pin(A/'check_source.py','6e9718f13e302f0f93b03320405bd76fc21e7ac1c11c0633585e5ee356375fb0')
receipt=pin(A/'observation.json','8adc9f00160b4f92f543ebcee3f480a4efdcdd43e125f36db039ab01c42ff9b0')
for f in ['Function.update v 13 (v 13-v 1)', '(hstrict : v 1<v 13)', 'tsub_pos_of_lt hstrict', 'P72Root.ι_tsub (le_of_lt hstrict)', 'rw [←cast_reverse v hstrict] at h', 'rw [←h]']:assert f in s,f
n=0
for F in range(1,40):
 for omega in range(F+1,50):
  t=max(0,omega-F);assert t>0 and t+F==omega;n+=1
assert max(0,5-5)==0

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
p=D/'reviews'/'ordinary14-88-to-87-positive-map-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'guard map source review; no Lean or unconditional reverse','finite_controls':n},sort_keys=True,indent=2))
