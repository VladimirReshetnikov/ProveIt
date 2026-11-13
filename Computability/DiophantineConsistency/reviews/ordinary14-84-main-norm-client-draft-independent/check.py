#!/usr/bin/env python3
"""Independent shared-DAG and source review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2]; A=D/'research/ordinary14-84-main-norm-client-draft'
def sha(d): return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes(); assert sha(d)==h,str(p); return d
src=pin(A/'MainNormClient.lean','58a05ca5998323ad4665ad03a3f0a580c579ed95b210dfc803ecfe8a9e48b767').decode()
pin(A/'check_source.py','650d182f58b4a3a62e2f4e37e6310fd60d358ca26a3a424e42210ff6545b50ff')
receipt=pin(A/'observation.json','30c6bbcc19aa3e67e5c6dc76c6686cc36437c1083711bf3f5c64f526eda6aaee')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-main-norm-client-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='0890fd5d709af73561be20547df6b8a726e08c8d26608448c46889f738c31132'
for path,h in {
 'ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean':'c3350a90b8fa909c208ad197acc7a3bbb15bd3e6d8e45ebf097645ae602ec02e',
 'ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean':'771cc1bf65a1d0e2b195627a45a4d152671ed0e86dbf12516855bfe8f1c11216',
 'ordinary14-84-85-zero-fields-draft/ZeroFields.lean':'75bb11893469673856b6fe02eba6f17317dfa8b4b65d35272577c42cf47b9c1e',
 'ordinary14-qcube84-lean-draft/P84QcubeGraph.lean':'552fa737fa0c36a58220053be90c4cdb35785d1fae53bc1c30bc15f8404104e9',
 'ordinary14-direct-pell79-lean-draft/P79DirectPell.lean':'e5b138f7ea6b5782d66fde5016726e01c9045bf5ba13858dad1d923ca9622cdb',
}.items(): pin(D/'research'/path,h)
g84=json.loads(pin(D/'research/ordinary14-qcube84-probe/candidate.json','cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61'))
g79=json.loads(pin(D/'research/ordinary14-direct-pell79/candidate.json','5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507'))
assert g84['witnesses']==g79['witnesses'] and g84['fixed_numerals']==g79['fixed_numerals']
def tree(g):
 rows={row[0]:row[1:] for row in g['source']}
 def visit(x):
  if x not in rows: return ('leaf',x)
  op,a,b=rows[x]; return (op,visit(a),visit(b))
 return visit('A1')
assert tree(g84)==tree(g79)
for f in ('(P84QcubeGraph.graph p).A1=(P79DirectPell.graph p).A1 := by rfl',
 '(hport : (p 0 : DiffRing V)=ι beta) (hs : 0<v 7)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 '(ZeroFields8485Draft.fields84 p v hz).2.1',
 'AuxGraphNormClientDraft.main_eval p beta v hport',
 'root_of_scaled_ring_square _ _ _ hU hsq'):
 assert f in src,f
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
assert not run.stderr and run.stdout==receipt
cases=0
for U in range(1,21):
 for Z in range(-80,81):
  for n in range(31):
   if Z*Z==U*U*n:
    assert abs(Z)%U==0 and (abs(Z)//U)**2==n
    cases+=1
assert 0*0==0*0*2 and all(d*d!=2 for d in range(3))
print(json.dumps({'scope':'shared-DAG and finite source review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'scaled_square_cases':cases,
 'zero_scale_boundary':True},sort_keys=True,indent=2))
