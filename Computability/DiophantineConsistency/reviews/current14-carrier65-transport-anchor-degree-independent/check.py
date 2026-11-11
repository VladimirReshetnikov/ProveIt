#!/usr/bin/env python3
import gzip,hashlib,json,math,random,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier65-transport-anchor-degree';source=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(source)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(source.read_bytes());rows=g['source'];by={r[0]:r for r in rows};assert len(rows)==65
for row in (['qm','*','beta','J'],['zqm','*','z','qm'],['Nt','-','transport_partial','zqm']):assert by[row[0]]==row
ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(source.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];data=gzip.decompress(z);assert len(data)==m['raw_bytes'] and hashlib.sha256(data).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(data,'big')
assert ports['beta']>0
dep={'z'}
for name,op,a,b in rows:
 if a in dep or b in dep:dep.add(name)
assert [r[0] for r in rows[:60] if r[0] in dep]==['zqm','Nt'];eligible=[r[0] for r in rows[:60] if r[0] not in dep];assert len(eligible)==58
P=1000000007;assert all(P%d for d in range(2,math.isqrt(P)+1));rng=random.Random(0xB128D);seen={t:[False,False] for t in eligible}
for sample in range(12):
 v={x:rng.randrange(1,P) for x in g['witnesses']};v.update({k:z%P for k,z in ports.items()});v.update({i:i for i in range(5)})
 for n,op,a,b in rows:
  x,y=v[a],v[b];v[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%P
 for t in eligible:
  seen[t][0]|=v[t]!=1;seen[t][1]|=v[t]!=(v['transport_partial']-1)%P
assert all(all(x) for x in seen.values())
res=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not res.stderr and json.loads(res.stdout)==json.loads((pkg/'result.json').read_text())
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-main-norm-shear-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','eligible':58,'z_dependent_preaggregation':2,'scope':'z-degree obstruction to direct original-node aliases with nonzero polynomial coefficient, no general zero-set or circuit lower bound claim'},indent=2))
