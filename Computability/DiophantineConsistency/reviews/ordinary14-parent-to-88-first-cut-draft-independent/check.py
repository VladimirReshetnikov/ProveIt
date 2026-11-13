#!/usr/bin/env python3
"""Independent parent→88 fresh first-root ring cut review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-parent-to-88-first-cut-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ParentTo88FirstCut.lean','fd493ab4dce4683d334344c70d1b5a8b7c98b2dab2395950c2f937247fad6695').decode()
pin(A/'check_source.py','2ba4f4a5895f6114572ff8b908b0ae99bdb1e154f7bd17164c6ee418d9864c5f')
receipt=pin(A/'observation.json','9810e721c56be3c33480780dc18a71094bf51046bdd972fef815c44e2d63adb0')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-parent-to-88-first-cut-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='f95403d5ab3759a93e197e627d204db0d880876b0cd111225f7b126a627c8b1e'
assert '(hY : Y=q3*s)' in s
assert '(q3*b)*(ell+k-(ell+k+s+tau))+Y*b=-(q3*b)*tau' in s
# Independent signed and zero-divisor ring instances of the exact identity.
n=0
for mod in (12,97):
 for q in range(5):
  for b in range(5):
   for ell in range(3):
    for k in range(3):
     for s0 in range(3):
      for tau in range(3):
       Y=q*s0
       assert ((q*b)*(ell+k-(ell+k+s0+tau))+Y*b+q*b*tau)%mod==0;n+=1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'parent-to-88 local ring cut source review; no Lean','finite_ring_controls':n},sort_keys=True,indent=2))
