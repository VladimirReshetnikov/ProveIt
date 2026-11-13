#!/usr/bin/env python3
"""Independent own-zero composition source review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-own-zero-main-balance-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'OwnZeroMainBalance.lean','4c98fabd9e270d181a6774bc61abd54f92a0b03dfaf680349d62f00e45351382').decode()
pin(A/'check_source.py','210c247ddc671bc61ed36b7b81090feacdedf45e29f17978f6a81df0c0e48253')
receipt=pin(A/'observation.json','26240764bd15d73b65d06aba9765a2abeeb6b3293794ee716542a8aeebc5143d')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-own-zero-main-balance-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='6602eb8aaf556524dfb0d22c9993dd064ffca1f127c977931ee9ce82f6169b02'
for path,h in {
 'ordinary14-84-natural-rank-draft/NaturalRank.lean':'d9f4c4911951201d5b3b0ed72c02bfc8e5d8b56dcd7dafc378e5273d0686a350',
 'ordinary14-84-main-balance-draft/MainBalance.lean':'b06ab81424dee0633ab4ad83d4fabc0a49c232f765f9e10401b74d46a3622a8b',
}.items():pin(D/'research'/path,h)
for f in ('(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)',
 '(hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)',
 '(hv : ∀ j, 0<v j) (hY : 8≤AuxGraphNormClientDraft.Y beta v)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'rank_of_84_zero p beta K MC MF v hbeta hK hMC hMF (hv 1) (hv 6) hz',
 'exact add_pos (hv 9) (hv 10)',
 'main_norm_and_balance p beta v R hbeta (hv 7) hY hk hR hz'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-natural-rank-draft-independent','ordinary14-84-main-balance-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'source composition review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'independent_dependency_reviews':2},sort_keys=True,indent=2))
