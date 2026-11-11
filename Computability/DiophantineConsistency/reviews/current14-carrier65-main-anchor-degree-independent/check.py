#!/usr/bin/env python3
import gzip,hashlib,json,math,random,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier65-main-anchor-degree';source=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(source)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(source.read_bytes());rows=g['source'];by={r[0]:r for r in rows};assert len(rows)==65
for row in (['a','+','E','Y'],['four_a','*',4,'a'],['H','+','four_a',3],['Delta','+','a2','H'],['ac','*','a','c'],['main_base','+','X','ac'],['gammaH','*','gamma','H'],['main_root','+','main_base','gammaH'],['main_square','*','main_root','main_root'],['Dc2','*','Delta','c2'],['N1','-','main_square','Dc2']):assert by[row[0]]==row
ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(source.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];data=gzip.decompress(z);assert len(data)==m['raw_bytes'] and hashlib.sha256(data).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(data,'big')
def ancestors(x):
 seen=set();todo=[x]
 while todo:
  v=todo.pop()
  if v in by and v not in seen:seen.add(v);todo.extend(by[v][2:])
 return seen
eligible=[r[0] for r in rows[:60] if r[0] not in ancestors('N1')];assert len(eligible)==37
dep={'gamma'}
for name,op,a,b in rows:
 if a in dep or b in dep:dep.add(name)
assert [r[0] for r in rows[:60] if r[0] in dep]==['gammaH','main_root','main_square','N1'] and not (set(eligible)&dep)
# At all-zero witnesses, H=3, proving H is a nonzero polynomial after fixed-port specialization.
vals={x:0 for x in g['witnesses']};vals.update(ports);vals.update({i:i for i in range(5)})
for n,op,a,b in rows:
 x,y=vals[a],vals[b];vals[n]=x+y if op=='+' else x-y if op=='-' else x*y
assert vals['H']==3
# Independent fixed-port modular nonidentity witnesses at independently chosen positive samples.
P=1000000007;assert all(P%d for d in range(2,math.isqrt(P)+1));rng=random.Random(0xA719D);seen={t:[False,False] for t in eligible}
for sample in range(12):
 v={x:rng.randrange(1,P) for x in g['witnesses']};v.update({k:z%P for k,z in ports.items()});v.update({i:i for i in range(5)})
 for n,op,a,b in rows:
  x,y=v[a],v[b];v[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%P
 for t in eligible:
  seen[t][0]|=v[t]!=1;seen[t][1]|=v[t]!=(v['Dc2']+1)%P
assert all(all(x) for x in seen.values())
res=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not res.stderr and json.loads(res.stdout)==json.loads((pkg/'result.json').read_text())
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-main-norm-shear-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','eligible':37,'gamma_dependent_preaggregation':4,'scope':'gamma-degree obstruction to direct original-node aliases with nonzero polynomial coefficient, not general circuit lower bound'},indent=2))
