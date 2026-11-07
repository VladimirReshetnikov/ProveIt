#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-abstract-target-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'d2afdfdcd2e8b35e4e99ce235f32684172e58b0cca6d333c3295015140662f75','source-manifest.json':'686f544b40fc9e6d4378e2d4f705d1bcc91645cc6f7d74e73d790b403557dcb6','src/DiophantineConsistency/Sign28AbstractTarget.lean':'a818e961d41e00c00f7617eab3ca2e8f238dfff5871b4efc0108d4ca7abd8425','partial-survey.py':'462acee066ec0a45fb30b682cc7d435a0b4b1414b9f8129c6f326ca3049ded8e','union-survey.py':'a2f88678529dfef74f0f93aebf5b9e62ee0830842571089b48e91f646b91ab12','union.json':'89b996196cb27d9ec751b673e8ac76e7b636a79ba2f5d03118982bd17e117651'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.Sign28CurrentConsIff'];s=(P/'src/DiophantineConsistency/Sign28AbstractTarget.lean').read_text()
for x in ['theorem transfer (T : Prop)','(h : (∃ w : Fin 31 → V','↔ T) :','(∃ w : Fin 28 → V','Iff.trans (Sign28CurrentConsIff.seed_cons_iff (V := V)) h','𝗜𝚺₁']:assert x in s
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'conditional arbitrary T transport only; concrete source equivalence remains an assumption'},sort_keys=True,indent=2))
