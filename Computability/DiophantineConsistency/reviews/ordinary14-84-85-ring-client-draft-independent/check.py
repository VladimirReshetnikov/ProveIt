#!/usr/bin/env python3
"""Independent source interface and finite ring controls; no Lean."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2]; A=D/'research/ordinary14-84-85-ring-client-draft'
def sha(data): return hashlib.sha256(data).hexdigest()
def pin(p,h):
 d=p.read_bytes(); assert sha(d)==h,str(p); return d
source=pin(A/'RingComparison.lean','a8cc5107975d92bf6ce121e1ec6e769140e393ccd5c38f86cba00db958223de9').decode()
pin(A/'check_source.py','c7c8583ad7d1aebb671c794b9aa7f9f1fc409164caaf63280c71c7acbe06d310')
receipt=pin(A/'observation.json','fa7aa6af5185ba92f2acf5a0380ec99470c6cea64b506fb72831dbb27855cf5f')
for path,h in [('ordinary14-qcube85-lean-draft/P85QcubeGraph.lean','46c5ffa3344d70b22ca9bc3c56a7b0ba37ac6603a3f7b38f202f5d84fc44ef9b'),('ordinary14-qcube84-lean-draft/P84QcubeGraph.lean','552fa737fa0c36a58220053be90c4cdb35785d1fae53bc1c30bc15f8404104e9')]: pin(D/'research'/path,h)
old=json.loads(pin(D/'research/ordinary14-qcube85-tradeoff/candidate.json','0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'))
new=json.loads(pin(D/'research/ordinary14-qcube84-probe/candidate.json','cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61'))
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-85-ring-client-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='d3e3ba7bb527151198f687dec66604a3c78e904d010e0f19afacbd396858c0eb'
for frag in ('import P84QcubeGraph','import P85QcubeGraph','[CommRing R]',
 'Function.update (Function.update v 6 ((1+v 0*(p 0 : R))*v 6)) 12 (v 12-v 6)',
 '(P85QcubeGraph.graph p).A0.evalRing (transform p v)',
 '(P85QcubeGraph.graph p).A1.evalRing (transform p v)',
 '(P85QcubeGraph.graph p).aux.evalRing (transform p v)',
 '(P85QcubeGraph.graph p).gap.evalRing (transform p v)',
 '(P85QcubeGraph.graph p).guardResidual.evalRing (transform p v)',
 '(P85QcubeGraph.graph p).output.evalRing (transform p v)'):
 assert frag in source,frag
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not run.stderr and run.stdout==receipt
def evaluate(g,initial,mod):
 v=initial.copy()
 for n,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x; y=v[y] if isinstance(y,str) else y
  value=x+y if op=='+' else x-y if op=='-' else x*y
  v[n]=value if mod is None else value%mod
 return v
rng=random.Random(20261111); cases=0
for mod in (None,4,6,9,12):
 for _ in range(120):
  v={name:rng.randrange(-5,6) for name in new['witnesses']+new['fixed_numerals']}
  n=evaluate(new,v,mod); o={name:v[name] for name in old['witnesses'] if name!='X'}
  o.update({name:v[name] for name in old['fixed_numerals']}); o['X']=n['X']; o['gamma']=v['gamma']-v['w']
  p=evaluate(old,o,mod)
  assert all(n[field]==p[field] for field in ('A0','A1','Fa','g72','guard','guarded_out'))
  cases+=1
print(json.dumps({'scope':'source and finite ring controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'ring_cases':cases,'composite_moduli':[4,6,9,12]},sort_keys=True,indent=2))
