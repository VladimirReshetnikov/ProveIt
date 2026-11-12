#!/usr/bin/env python3
"""Independent q-cubed bound source/finite review; no Lean invocation."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-qcube-size-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'QCubeSize.lean','6553261e396c24659988420260324bc19911ade97854405e863db4bfb6e510cc').decode()
pin(A/'check_source.py','48d6bb86ccd5c41c0c3d6ea75968ad04576e72c8ad02d1f04e7d029d1027e6b3')
receipt=pin(A/'observation.json','de2381cc912fd52ae1e4569c85dc8aeb6b198e6a20e8cf219d643523caeae823')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-qcube-size-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='2d15a3c5c44cfff201f61a1b9177646b3b01dfff070b4280612405a1f6da9835'
pin(D/'research/ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean','c3350a90b8fa909c208ad197acc7a3bbb15bd3e6d8e45ebf097645ae602ec02e')
for f in ('(hbeta : 0<beta) (hJ : 0<v 0) (hs : 0<v 7)',
 'have hp1 : 1≤v 0*beta := pos_iff_one_le.mp hprod',
 'mul_le_mul hq hq (by norm_num : (0:V)≤2)',
 'mul_le_mul hq hq2 (by norm_num : (0:V)≤4)',
 'have hs1 : 1≤v 7 := pos_iff_one_le.mp hs',
 '8≤AuxGraphNormClientDraft.Y beta v'):
 assert f in src,f
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
assert not r.stderr and r.stdout==receipt
cases=0
for beta,J,s in itertools.product(range(1,14),repeat=3):
 q=1+J*beta;Y=q*(q*q)*s
 assert q>=2 and q*q>=4 and q*(q*q)>=8 and Y>=8
 cases+=1
assert (1+1*1)**3==8
assert (1+0*1)**3*1<8 and (1+1*0)**3*1<8 and (1+1*1)**3*0<8
print(json.dumps({'scope':'source and finite size controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'positive_cases':cases,
 'sharp_boundary':True,'zero_hypothesis_boundaries':True},sort_keys=True,indent=2))
