#!/usr/bin/env python3
"""Independent first-index source and Pell controls; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-first-index-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'FirstIndex.lean','173e8ad4c0f26668c39e4067c99d222d49417969da7b41dd6eda96eb502ed14f').decode()
pin(A/'check_source.py','1d4a44c3acd959cc96e5253617d5c2c1e695af37c73e9d8983b743ae92c33b9f')
receipt=pin(A/'observation.json','3a91610eb2b7c3f2da741bd416583a9ca1ca9484c851ad0e6825ac154f600798')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-first-index-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='52f72552992ab7e0d68f0cea3f10c5639d34f52871c38d35843cba83b0ca2958'
pin(D/'research/ordinary14-84-first-norm-client-draft/FirstNormClient.lean','557f24cb4cc6184a3830feb01f4d70a7c228929c1f264d6dd79c07ab15b25142')
pin(D/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean','374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5')
for f in ('(hbeta : 0<beta) (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'let Q := (X beta v*Y beta v)*Y beta v',
 '∃ n : V, n≤K ∧ xcoord n (2*(Q-1)+1)=tau ∧',
 '2*ycoord n (2*(Q-1)+1)=K',
 'first_norm p beta v hbeta hJ hport hz',
 'positive_parameter_solution Q tau K hQ hnorm'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-84-first-norm-client-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=0
for Q in range(1,25):
 b=2*(Q-1)+1;x,y=1,0
 for n in range(7):
  k=2*y;ell=Q*k
  assert n<=k and x*x==1+Q*(Q+1)*k*k==1+ell*(ell+k)
  x,y=(b+2)*x+(b+1)*(b+3)*y,x+(b+2)*y
  cases+=1
print(json.dumps({'scope':'source and finite Pell controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'pell_controls':cases,
 'zero_index_included':True},sort_keys=True,indent=2))
