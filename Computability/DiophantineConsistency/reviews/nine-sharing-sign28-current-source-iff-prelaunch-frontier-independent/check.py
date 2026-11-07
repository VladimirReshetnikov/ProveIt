#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-current-source-iff-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'79ffeeaa57b6aca316ea6b3609b9bfb91606d0d153e48b9b1507dd19fb77dbad','source-manifest.json':'0082f60fc048fb4ea85914c4cb534c74ef82125a26931342e411d46f75a8fe6d','union-survey.py':'a2f88678529dfef74f0f93aebf5b9e62ee0830842571089b48e91f646b91ab12','union.json':'89b996196cb27d9ec751b673e8ac76e7b636a79ba2f5d03118982bd17e117651','src/DiophantineConsistency/Sign28CurrentSourceIff.lean':'fb7e0570ce92707814417ecc10dffe1380ebcb7b60e95abd78c0c3026ba64254'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.Sign28CurrentSeedIff','DiophantineConsistency.Sign31CurrentSourceIff']
s=(P/'src/DiophantineConsistency/Sign28CurrentSourceIff.lean').read_text()
for a in ['∃ w : Fin 28 → V','Fin.cons (1 : V) w','∃ u : Fin 14 → V','ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u','Sign28CurrentSeedIff.exists_same_input (1 : V)','h31.symm.trans Sign31CurrentSourceIff.seed_exists_iff_source','𝗜𝚺₁']:assert a in s
for rel,h in [('nine-sharing-sign28-current-iff-terminal-frontier-independent/check.py','c1123b8aa4ed290bc85e1a22727ee12449b5b3e6736871c90bef32896635c9c5')]:
 f=D/'reviews'/rel;assert H(f)==h;subprocess.run([sys.executable,'-I','-S','-B',str(f)],check=True,capture_output=True,timeout=30)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'proposed 28-coordinate current seed iff 14-coordinate current source in IΣ₁; no endpoint claim'},sort_keys=True,indent=2))
