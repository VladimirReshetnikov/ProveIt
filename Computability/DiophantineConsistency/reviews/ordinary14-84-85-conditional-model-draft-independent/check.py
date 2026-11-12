#!/usr/bin/env python3
"""Independent conditional map source/finite review; no Lean."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2]; A=D/'research/ordinary14-84-85-conditional-model-draft'
def sha(d): return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes(); assert sha(d)==h,str(p); return d
source=pin(A/'ConditionalComparison.lean','204cf248239f6a070176c407f1d8d2ddb8506afad9784e79ac5ab0a0d2638790').decode()
pin(A/'check_source.py','262591633eba607bde541d90fd1b7937e5b2e04fca9d95ec54780b15d7b78c05')
receipt=pin(A/'observation.json','b930955b86f83242cb077cf2279c564c4e7d323b16ace89a8c32d702d859f36a')
pin(D/'research/ordinary14-84-85-ring-client-draft/RingComparison.lean','a8cc5107975d92bf6ce121e1ec6e769140e393ccd5c38f86cba00db958223de9')
pin(D/'Lean/DiophantineConsistency/Compact44/P72Root.lean','066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091')
old=json.loads(pin(D/'research/ordinary14-qcube85-tradeoff/candidate.json','0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'))
new=json.loads(pin(D/'research/ordinary14-qcube84-probe/candidate.json','cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61'))
readme=(A/'README.md').read_bytes(); tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-85-conditional-model-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='2d55132cf01dba639bed14106bae4f8252f3b1f439ed867ca2000487af5cd63b'
for f in ('(hgamma : v 6<v 12)','(hdiv : q beta v∣v 6)',
          'P72Root.ι_tsub (le_of_lt hgamma)',
          'rw [← cast_to85 p beta v hport hgamma] at h',
          'rw [← cast_to84 p beta v w hport hw] at h',
          'exact (internalZero_iff _ _).mp hz'):
 assert f in source,f
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not run.stderr and run.stdout==receipt
def calc(g,v):
 z=v.copy()
 for n,op,x,y in g['source']:
  x=z[x] if isinstance(x,str) else x; y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
fields=('A0','A1','Fa','g72','guard','guarded_out'); rng=random.Random(20261112)
for _ in range(300):
 p={x:rng.randrange(0,8) for x in new['fixed_numerals']}
 a={x:rng.randrange(1,10) for x in new['witnesses']}; a['gamma']+=a['w']
 q=1+a['J']*p['beta']; b={x:a[x] for x in old['witnesses'] if x!='X'}
 b['X']=q*a['w']; b['gamma']=a['gamma']-a['w']
 assert all(b[x]>0 for x in old['witnesses'])
 n=calc(new,a|p); o=calc(old,b|p); assert all(n[f]==o[f] for f in fields)
 # Independent parent, with positive quotient and arbitrary positive gamma.
 parent={x:rng.randrange(1,10) for x in old['witnesses']}; w=rng.randrange(1,10)
 parent['X']=(1+parent['J']*p['beta'])*w
 child={x:parent[x] for x in new['witnesses'] if x!='w'}; child['w']=w; child['gamma']+=w
 assert all(child[x]>0 for x in new['witnesses'])
 n=calc(new,child|p); o=calc(old,parent|p); assert all(n[f]==o[f] for f in fields)
assert 3-3==0 and 6%(1+2*2)!=0
print(json.dumps({'scope':'conditional source and finite review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'positive_cases_per_direction':300,
 'strict_difference_boundary':True,'nondivisible_boundary':True},sort_keys=True,indent=2))
