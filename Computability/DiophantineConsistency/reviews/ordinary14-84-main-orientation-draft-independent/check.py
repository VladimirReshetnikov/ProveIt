#!/usr/bin/env python3
"""Independent conditional orientation source and finite review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2]; A=D/'research/ordinary14-84-main-orientation-draft'
def sha(d): return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes(); assert sha(d)==h,str(p); return d
src=pin(A/'MainOrientation.lean','33887b86870acc88bce72c91db03a355156ddf8980a48de55dfe4144d7dface4').decode()
pin(A/'check_source.py','0a7adfdc5390fe0f8f550cc6f75d596e8db5e883c7357a723e065e35f82c2886')
receipt=pin(A/'observation.json','1dc1fd21e55b49e98eef953b3c13f71519c944ef33d97a1c166dfe1b231ce72a')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-main-orientation-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='ab1f1c7d17716543b64e1f5bc85d95cd8732daaed11a1c09ab147e83475a9201'
for path,h in {
 'ordinary14-84-signed-main-norm-draft/SignedMainNorm.lean':'b674de377bdae3155ffb46b1711971425a68cdaa1ac9134c608a3233bc8c5e8b',
 'ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean':'d16c6dca1f5bb5240db5e2b72d6d1895568c9e178c933a68e92f82b6be2be43e',
 'ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean':'c3350a90b8fa909c208ad197acc7a3bbb15bd3e6d8e45ebf097645ae602ec02e',
}.items():pin(D/'research'/path,h)
pin(D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998')
for f in ('(hport : (p 0 : DiffRing V)=ι beta) (hs : 0<v 7)',
 '(hY : 8≤AuxGraphNormClientDraft.Y beta v)',
 '(hk : 0<AuxGraphNormClientDraft.k v)',
 '(hR : AuxGraphNormClientDraft.rank p beta v=ι R)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'modified_main_parts_positive U X Y k (v 9) (v 12) R hU hY hk',
 'ι_lt_ι.mpr hparts','sub_pos.mpr hlt',
 'signed_main_root p beta v hport hs hz','neg_nonpos.mpr (ι_nonneg _)'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-signed-main-norm-draft-independent','ordinary14-modified-carrier-model-facts-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
cases=0
for U in range(1,4):
 for X in range(5):
  for Y in range(8,12):
   for k in range(1,5):
    for eta in range(3):
     for gamma in range(3):
      for R in range(4):
       a=X*Y+Y;c=eta+Y*k;H=3+4*a
       L=U*(X+a*c)+H*(U*gamma+R+1);N=H*k
       assert L>N and L-N==U*(X+a*c)+H*(U*gamma-(k-R-1))
       cases+=1
print(json.dumps({'scope':'conditional source and finite review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'inequality_cases':cases,
 'independent_dependency_reviews':2},sort_keys=True,indent=2))
