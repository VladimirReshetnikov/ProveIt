#!/usr/bin/env python3
"""Independent 87 source interface review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-growth-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'Growth87.lean','813b53cee5585aae543e521309c2f93493c8a239ee6a07646aa5a7b422cfb231').decode()
pin(A/'check_source.py','0dbf026e6aa3da5ccc50b39bbd004fb54fe08feee5b905f7fa1a4a38a43fd76f')
receipt=pin(A/'observation.json','a81e951b49e488d9043603f35ee14c439089434b31d3144a4daf58ede13a4562')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n' b'`../../reviews/ordinary14-87-growth-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='c186a246b0ed4dedc8e4a10ed69acc88d67d48e0cccdda5a3d5842354379451d'
for f in ['(hbeta46 : 46≤beta)', 'Divides3X87Draft.divides_three_X p beta K MC MF v', 'Arithmetic.le_of_dvd (mul_pos (by simp) (hv 6)) hdiv', 'let r : V := n-1', 'power_bound xx yy r kk cc (v 9) (v 10) hX', 'Exp.exp (naturalRank beta MC MF v)<Y v']:assert f in s,f
n=0
for q in range(47,130):
 for X in range(1,100):
  if 3*X%q==0:
   assert X>=16;n+=1

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
p=D/'reviews'/'ordinary14-87-divides-3x-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero source interface review; no Lean','finite_controls':n},sort_keys=True,indent=2))
