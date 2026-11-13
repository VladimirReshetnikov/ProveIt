#!/usr/bin/env python3
"""Independent 87 own-zero four-field source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-four-fields-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'FourFields87.lean','11c332e1ca71b9c79592295d4dd243d4ae2c43fca751ca37c78f2a36eb01ab23').decode()
pin(A/'check_source.py','ac0346c27feeda32adf8f2c3a7650eb5af7aa50f655b264efe4f6ab25f6317cb')
receipt=pin(A/'observation.json','ff57dfaa158fe325eb57bba8b0588e8a2c66b707129fafffffe6b2a33ce957ad')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-four-fields-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='8f488fd1f05af1a30d7becbc9ecdc4c880c27ef6613b82b809ff25a2eb3e29be'
for f in ('(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 '(eval (P87ShiftedGuard.graph p).aux v-1)',
 'rw [hs.1,hs.2.1,hs.2.2.1,hs.2.2.2] at hf',
 'exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩'):
 assert f in s,f
assert 'InternalZero (P86ResidueGraph.graph p).output' not in s
old=json.loads((D/'research/ordinary14-shifted-guard87-probe/candidate.json').read_bytes())
new=json.loads((D/'research/ordinary14-residue-guard86/candidate.json').read_bytes())
def shape(g,field):
 rows={r[0]:r[1:] for r in g['source']};seen={};stack=[field]
 while stack:
  k=stack.pop()
  if k not in rows or k in seen:continue
  op,x,y=rows[k];seen[k]=(op,x,y)
  stack.extend(z for z in (x,y) if isinstance(z,str))
 return seen
for f in ('A0','A1','Fa','g72'):assert shape(old,f)==shape(new,f),f
assert shape(old,'guard')!=shape(new,'guard')
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-87-first-quotient-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero shared-field source review; no Lean or 86 zero',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'matching_non_guard_fields':4},sort_keys=True,indent=2))
