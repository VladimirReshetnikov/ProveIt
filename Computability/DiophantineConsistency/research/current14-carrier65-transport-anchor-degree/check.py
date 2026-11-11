#!/usr/bin/env python3
"""Pins and modular nonidentity witnesses for a z-degree alias obstruction."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);rows=g['source'];edges={r[0]:r for r in rows};ports={}
for name,meta in g['coefficient_binding']['ports'].items():
 z=(p.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['gzip_sha256']
 b=gzip.decompress(z);assert hashlib.sha256(b).hexdigest()==meta['raw_sha256'];ports[name]=int.from_bytes(b,'big')
assert ports['beta']>0 and edges['qm']==['qm','*','beta','J']
assert edges['zqm']==['zqm','*','z','qm'] and edges['Nt']==['Nt','-','transport_partial','zqm']
dep={'z'}
for name,op,a,b in rows:
 if a in dep or b in dep:dep.add(name)
assert [r[0] for r in rows[:60] if r[0] in dep]==['zqm','Nt']
eligible=[r[0] for r in rows[:60] if r[0] not in dep];assert len(eligible)==58
primes=(1000000007,1000000009,998244353);rng=random.Random(0x7A16); observations={x:[None,None] for x in eligible}
for p0 in primes:
 assert all(p0%d for d in range(2,int(p0**.5)+1))
 for sample in range(4):
  vals={v:rng.randrange(1,p0) for v in g['witnesses']};vals.update({k:v%p0 for k,v in ports.items()});vals.update({i:i for i in range(5)})
  for name,op,a,b in rows:
   x,y=vals[a],vals[b];vals[name]=(x+y if op=='+' else x-y if op=='-' else x*y)%p0
  for t in eligible:
   for j,target in enumerate((1,(vals['transport_partial']-1)%p0)):
    if observations[t][j] is None and vals[t]!=target:
     observations[t][j]={'prime':p0,'sample':sample,'residue_difference':(vals[t]-target)%p0}
assert all(all(x is not None for x in obs) for obs in observations.values())
print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'z_dependent_preaggregation':['zqm','Nt'],'eligible_count':len(eligible),'modular_nonidentity_witnesses':observations,'scope':'z-degree obstruction to direct preaggregation aliases, not a circuit lower bound'},sort_keys=True,indent=2))
