#!/usr/bin/env python3
"""Independent strong-field source and finite review; no Lean invocation."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-strong-norm-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'StrongNorm.lean','18097a1230b0f935bda91a82b5ad314a64b05f9e6b07c3436f18e5cc95aa7a0d').decode()
pin(A/'check_source.py','311edd0823f8622d26aea56c3fe5875a14eafe018603cc48321c9be92fb5d658')
receipt=pin(A/'observation.json','8585a98ca81bc5fd5ef68ab5e6775eca1d6fe5fbaa0e4cd571785a42e86b3fd7')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-strong-norm-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='c3f157385959179fbf02c6b742234a044bfdcfb0d7ea0857463519877a830e45'
for path,h in {
 'ordinary14-84-85-zero-fields-draft/ZeroFields.lean':'75bb11893469673856b6fe02eba6f17317dfa8b4b65d35272577c42cf47b9c1e',
 'ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean':'c3350a90b8fa909c208ad197acc7a3bbb15bd3e6d8e45ebf097645ae602ec02e',
 'ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean':'771cc1bf65a1d0e2b195627a45a4d152671ed0e86dbf12516855bfe8f1c11216',
}.items():pin(D/'research'/path,h)
g84=json.loads(pin(D/'research/ordinary14-qcube84-probe/candidate.json','cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61'))
g79=json.loads(pin(D/'research/ordinary14-direct-pell79/candidate.json','5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507'))
assert g84['witnesses']==g79['witnesses'] and g84['fixed_numerals']==g79['fixed_numerals']
def tree(g):
 rows={row[0]:row[1:] for row in g['source']}
 def visit(x):
  if x not in rows:return ('leaf',x)
  op,a,b=rows[x];return (op,visit(a),visit(b))
 return visit('g72')
assert tree(g84)==tree(g79)
for f in ('(hport : (p 0 : DiffRing V)=ι beta)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 '(v 4*c*c)*(v 4*c*c)+Delta=Delta*(v 3*v 3)',
 '(ZeroFields8485Draft.fields84 p v hz).2.2.2.1',
 'rw [shared_strong p] at hg','AuxGraphNormClientDraft.strong_eval p beta v hport',
 'strong_norm_of_ring_residual _ _ _ _ hg'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-84-85-zero-fields-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
def calc(v):
 z=v.copy()
 for n,op,x,y in g84['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
rng=random.Random(8401091)
for _ in range(500):
 v={n:rng.randrange(-4,5) for n in g84['witnesses']+g84['fixed_numerals']}
 z=calc(v);q=1+v['J']*v['beta'];X=q*v['w'];Y=q**3*v['s']
 a=X*Y+Y;c=v['eta']+Y*(v['eta']+v['zeta']);delta=3+4*a+a*a
 assert z['g72']==(v['i']*c*c)**2-delta*(v['f']**2-1)
 assert (z['g72']==0)==((v['i']*c*c)**2+delta==delta*v['f']**2)
print(json.dumps({'scope':'source and finite strong-field controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'signed_formula_cases':500},sort_keys=True,indent=2))
