#!/usr/bin/env python3
"""Pins and modular nonidentity witnesses for a general gamma-degree lemma."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);rows=g['source'];edges={r[0]:r for r in rows}; ports={}
for name,meta in g['coefficient_binding']['ports'].items():
 z=(p.parent/'coefficients'/meta['file']).read_bytes(); assert hashlib.sha256(z).hexdigest()==meta['gzip_sha256']
 b=gzip.decompress(z);assert hashlib.sha256(b).hexdigest()==meta['raw_sha256'];ports[name]=int.from_bytes(b,'big')
def ancestors(v):
 seen=set();todo=[v]
 while todo:
  x=todo.pop()
  if x in edges and x not in seen:seen.add(x);todo.extend(edges[x][2:])
 return seen
assert edges['H']==['H','+','four_a',3] and edges['four_a']==['four_a','*',4,'a']
assert edges['main_root']==['main_root','+','main_base','gammaH']
assert edges['gammaH']==['gammaH','*','gamma','H']
assert edges['main_square']==['main_square','*','main_root','main_root']
assert edges['N1']==['N1','-','main_square','Dc2']
anc=ancestors('N1'); eligible=[r[0] for r in rows[:60] if r[0] not in anc]
assert len(eligible)==37
# Structural propagation of gamma occurrence; conservative in the presence of cancellation.
dep={'gamma'}
for name,op,a,b in rows:
 if a in dep or b in dep:dep.add(name)
assert not(set(eligible)&dep)
assert [r[0] for r in rows[:60] if r[0] in dep]==['gammaH','main_root','main_square','N1']
primes=(1000000007,1000000009,998244353);rng=random.Random(0xC0E11A); observations={x:[None,None] for x in eligible}
for p0 in primes:
 assert all(p0%d for d in range(2,int(p0**.5)+1))
 for sample in range(4):
  vals={v:rng.randrange(1,p0) for v in g['witnesses']};vals.update({k:v%p0 for k,v in ports.items()});vals.update({i:i for i in range(5)})
  for name,op,a,b in rows:
   x,y=vals[a],vals[b];vals[name]=(x+y if op=='+' else x-y if op=='-' else x*y)%p0
  for t in eligible:
   for j,target in enumerate((1,(vals['Dc2']+1)%p0)):
    if observations[t][j] is None and vals[t]!=target:
     observations[t][j]={'prime':p0,'sample':sample,'residue_difference':(vals[t]-target)%p0}
assert all(all(x is not None for x in obs) for obs in observations.values())
print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'gamma_dependent_preaggregation':['gammaH','main_root','main_square','N1'],'eligible_count':len(eligible),'modular_nonidentity_witnesses':observations,'scope':'gamma-degree obstruction to direct preaggregation aliases, not a circuit lower bound'},sort_keys=True,indent=2))
