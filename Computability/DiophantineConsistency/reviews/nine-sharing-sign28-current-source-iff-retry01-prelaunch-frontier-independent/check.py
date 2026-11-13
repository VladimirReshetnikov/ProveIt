#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-current-source-iff-retry01';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'8c65ffe92373f0b853119543e475fea5cb50d2f19d0863f75bf3b5fbb3b8beb0','source-manifest.json':'ffddca8b0c92f47a2ca65eaed89804caaf65d44a2dcf44262d292432241b629d','union-survey.py':'a2f88678529dfef74f0f93aebf5b9e62ee0830842571089b48e91f646b91ab12','union.json':'89b996196cb27d9ec751b673e8ac76e7b636a79ba2f5d03118982bd17e117651'}.items():assert H(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(rows)==2 and rows[0]['imports']==['DiophantineConsistency.Sign28CurrentSeedIff'] and rows[1]['imports']==['DiophantineConsistency.Sign28CurrentConsIff','DiophantineConsistency.Sign31CurrentSourceIff'];ss=[]
for r in rows:
 f=P/'src/DiophantineConsistency'/(r['module'].split('.')[-1]+'.lean');assert H(f)==r['source_sha256'];ss.append(f.read_text())
a,b=ss;old=(D/'research/nine-sharing-sign28-current-source-iff-check/src/DiophantineConsistency/Sign28CurrentSourceIff.lean').read_text();assert b.split('theorem seed_exists_iff_source',1)[1].split(':=',1)[0]==old.split('theorem seed_exists_iff_source',1)[1].split(':=',1)[0]
for x in ['Fin.tail v','Fin.cons_self_tail v','exists_cons_iff (V := V)','Sign28CurrentSeedIff.exists_same_input (1 : V)','h31.symm']:assert x in a
assert 'Sign28CurrentConsIff.seed_cons_iff.trans Sign31CurrentSourceIff.seed_exists_iff_source' in b and all('attribute [local irreducible]' in s and '𝗜𝚺₁' in s for s in ss)
review=D/'reviews/nine-sharing-sign28-current-source-iff-failure-frontier-independent/check.py';assert H(review)=='a1962b4cd21b0fed26782090d5ff92156f2b320cdd5d8ea51c1787d5de6f0e10';subprocess.run([sys.executable,'-I','-S','-B',str(review)],capture_output=True,check=True,timeout=60)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':2,'scope':'proposed factored Fin28 seed iff Fin14 source in IΣ₁; previous memory cause unknown'},sort_keys=True,indent=2))
