#!/usr/bin/env python3
"""Independent 85 guard/rank source and finite review; no Lean."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-guard-rank-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'GuardRank85.lean','e9eb6ebef3d35dfa2324e00e16a068f7ad67e680f79ebee3a4f8af156e3c6d55').decode()
pin(A/'check_source.py','6583890c21c6930ae814be3c7389fe19395c0e1f08a9e675a6ee5aaa23de7624')
receipt=pin(A/'observation.json','be075efec70e464631c999e3c626d398aab92e9abad6ca4b6617a55f17246b15')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-guard-rank-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='49a519136fb1a392ee5edb8d74949914683db9a8015773f88cdc16159d412ac2'
pin(D/'research/ordinary14-84-natural-rank-draft/NaturalRank.lean','d9f4c4911951201d5b3b0ed72c02bfc8e5d8b56dcd7dafc378e5273d0686a350')
pin(D/'research/ordinary14-qcube85-lean-draft/P85QcubeGraph.lean','46c5ffa3344d70b22ca9bc3c56a7b0ba37ac6603a3f7b38f202f5d84fc44ef9b')
g=json.loads(pin(D/'research/ordinary14-qcube85-tradeoff/candidate.json','0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'))
for f in ('(ι (v 6)+ι K)-ι (v 1)-ι (v 0*beta)*ι (v 13)',
 'let X := v 6','(ZeroFields8485Draft.fields85 p v hz).2.2.2.2',
 '(hz : InternalZero (P85QcubeGraph.graph p).output v)',
 'gap_of_85_zero p beta K v hbeta hK hFpos hX hz',
 'NaturalRank84Draft.rank_repr p beta MC MF v hMC hMF hF hq2'):
 assert f in src,f
assert 'fields84' not in src and 'AuxGraphNormClientDraft.X' not in src and 'FreeJ' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-qcube85-lean-draft-independent','ordinary14-84-natural-rank-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
def calc(v):
 z=v.copy()
 for n,op,x,y in g['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
rng=random.Random(8501011);nondiv=0
for _ in range(500):
 v={n:rng.randrange(1,8) for n in g['witnesses']};v.update({n:rng.randrange(0,8) for n in g['fixed_numerals']})
 q=1+v['J']*v['beta'];v['F']=rng.randrange(q+1);z=calc(v)
 assert z['guard']==(q-v['F']-v['alpha'])*(v['X']+v['K0'])-v['F']-v['J']*v['beta']*v['h']
 assert z['R']==(v['alpha']+(q-v['F'])*v['J']*v['beta'])*(q*q-1)+v['J']*(v['MC']+v['MF']*q)
 nondiv+=v['X']%q!=0
assert nondiv
print(json.dumps({'scope':'source and finite graph controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'literal_controls':500,
 'X_not_divisible_by_q':nondiv},sort_keys=True,indent=2))
