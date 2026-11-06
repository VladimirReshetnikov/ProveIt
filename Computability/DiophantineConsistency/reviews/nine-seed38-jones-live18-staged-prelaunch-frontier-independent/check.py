#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-live18-staged-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'9de3f705bb3e528fe43fd3241504cbe268beac5f98f85d1128dcce7a416cc8b0','provider_preflight.py':'0b89b76fc5e0b1a7358cf5f2d8455c259706ed53b0df39d1aeee2d5b060e084f','source-manifest.json':'85ed34a0150a6824684298774584a2b679e2ed516ac5fc92d4a944e940455a22'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows'];hashes=['a218f74792b1c97d9c58fe4fa18b816392038faf89684649124e7389549a9d32','37faad23da93c1f8c88bcd9fd7759f33b315b91b5f0996adb9c578cfe7b4e2c8','7d753c75b74fe692481e447736b8bb83bbfe683b12c083ae1acbc32aeb286356','57b121e8e47a5babed07ef2da168f96d679a7abeda421049de2c0261d45d300f'];groups=[['b','N','g'],['G','R','h'],['s','w','phi'],['i','j']];index={'b':0,'N':3,'g':7,'G':9,'R':10,'h':11,'s':12,'w':13,'phi':14,'i':15,'j':16};assert len(rows)==4
for i,(row,sha,ts) in enumerate(zip(rows,hashes,groups),1):
 n='Norm38MacroLive18Group%02d'%i;q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n;assert row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Norm38MacroRankSymbolic'];names=['d18_'+t+'_carry' for t in ts];assert re.findall(r'^theorem (\w+)',s,re.M)==names and re.findall(r'^#print axioms (\w+)',s,re.M)==names
 for t in ts:
  block=s.split('theorem d18_'+t+'_carry',1)[1].split(':= by',1)[0];v=re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',block);assert len(v)==2 and int(v[0][0])==18 and int(v[0][1])==index[t] and int(v[1][1])==index[t] and all(int(a)==int(b)+1+c.count('.castSucc') for a,b,c in v)
for row in rows:
 s=(p/'src/DiophantineConsistency'/(row['module'].split('.')[-1]+'.lean')).read_text()
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
f=d/'research/nine-seed38-jones-compact-macro-prototype/recipe.json';assert h(f)=='779cd1d65dd84a4d5db6dd2072e94a7807b35394f5c245917b3688cc8ab2c090';recipe=json.loads(f.read_text());first=[x['name'] for x in recipe['nodes'][:18]];refs=set();stack=[x['expr'] for x in recipe['nodes'][18:]]+[recipe['output']]
while stack:
 x=stack.pop()
 if isinstance(x,list):
  if len(x)==2 and x[0]=='ref':refs.add(x[1])
  else:stack.extend(x)
assert {x for x in first if x in refs}==set(index)|{'t'} and first[17]=='t'
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==4
print(json.dumps({'status':'PASS','preflight':o,'live_entries':12,'carry_theorems':11,'scope':'uncompiled d18 carry identities; external recipe liveness only; no Lean replay'},sort_keys=True,indent=2))
