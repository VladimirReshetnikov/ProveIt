#!/usr/bin/env python3
"""Independent 86 own-zero quotient source/finite review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-86-ownzero-quotient-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'OwnZeroQuotient86.lean','432175bbc89d27b0cbffe902ac12c00e143d3e473cb02a42280893dfcb94e9c7').decode()
pin(A/'check_source.py','cf1121d0e1ea3c1c3bfcbe2caf49655cd231f0114b157f790cf98a51928cdbbc')
receipt=pin(A/'observation.json','21f1eda0c9c9ede23eac3c73a8a032c8a1451af557f1aeac1200c7cf82fbd9b0')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-86-ownzero-quotient-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='253a0dcc9111ed62a0c4e57d5510ac27ea607fa0135c3218b93b32940074e2b8'
for path,h in {
 'ordinary14-86-first-fields-draft/FirstFields86.lean':'bf15b71df553f656344d8898a1615fd466c6f31115ca7c2dfaea55bffef407f3',
 'ordinary14-85-86-quotient-facts-draft/QuotientFacts.lean':'5e45d7e5e75e6a4a9615a036b27872554f2cdc68af37d6e1ac0617599c86aa74',
}.items():pin(D/'research'/path,h)
for f in ('(hbeta : 0<beta) (hJ : 0<v 0) (hY : 0<v 7)',
 '(hport : (p 0 : DiffRing V)=ι beta)','(hz : InternalZero (P86ResidueGraph.graph p).output v)',
 'have hf := (fields_of_zero p v hz).1','rw [first_eval p beta v hport] at hf',
 'QCubeQuotientFactsDraft.quotient_and_root (b beta v) (v 7) (firstP v) (v 8)',
 '(radicand v) hb hY hD'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-86-first-fields-draft-independent','ordinary14-85-86-quotient-facts-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
cases=positive=negative=0
for b in range(1,7):
 q=1+b;Q=q**3;M=Q*b
 for X in range(1,4):
  for s in range(1,4):
   Y=Q*s;k=2;ell=X*Y*Y*k;P=ell+k;D0=1+ell*P;tau=2*X*Y*Y+1
   assert tau*tau==D0
   for sign in (-1,1):
    r=P+s+sign*tau;z=M*(P-r)+b*Y
    assert r>0 and z*z==M*M*D0 and abs(z)==M*tau
    positive+=z>0;negative+=z<0;cases+=1
assert positive and negative
print(json.dumps({'scope':'source and finite first-residual controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'partial_first_norm_cases':cases,
 'positive_signed_roots':positive,'negative_signed_roots':negative},sort_keys=True,indent=2))
