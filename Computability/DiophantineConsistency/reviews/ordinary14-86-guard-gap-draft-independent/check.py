#!/usr/bin/env python3
"""Independent 86 guard-gap source review; no Lean."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-86-guard-gap-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'GuardGap86.lean','6216d2da06df423665ca3816dfd42647b3b6e3edda033a49db8529aa275405d4').decode()
pin(A/'check_source.py','ab2d845ad1b7ae947c3ccf839fbd6ae683e771abbf0c4d6c0900cc0f82deabff')
receipt=pin(A/'observation.json','21e5f3baf9d385f43cd74b62f039dbb3b1a4a2a203e896d470a2a666d290fb3b')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-86-guard-gap-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='f3f2574eddc124e1da8cad15e1a70979d6ec7f27f039f9a124870a8454333711'
for f in ('(hbeta : (p 0 : DiffRing V)=ι beta)','(hK : (p 1 : DiffRing V)=ι K)',
 '(hF : 0<v 1) (hw : 0<v 6)','FirstFields86Draft.fields_of_zero p v hz',
 '(ι (v 6)+ι K)-ι (v 1)-ι (v 0*beta)*ι (v 13)',
 'mul_nonpos_of_nonpos_of_nonneg','exact ι_lt_ι.mp hlt'):
 assert f in s,f
n=0
for q,F,a,X,K,b,h in itertools.product(range(1,10),range(1,5),range(5),range(1,5),range(4),range(5),range(5)):
 if (q-F-a)*(X+K)-F-b*h==0:
  n+=1;assert F+a<q
assert n>0
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'source and finite guard review only; no Lean','prelink_readme_sha256':sha(r[:-len(tail)]),'bounded_guard_zeros':n},sort_keys=True,indent=2))
