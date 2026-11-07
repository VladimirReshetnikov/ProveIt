#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-jones-source-iff-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'9ba00d6053306dd408e80d5ceabec764eb7c86d24a1a6a96d3a9613f98fa8b44','provider_survey.py':'1aca0a18dab3e87c27922f058a9cb275654a7cbd48ce69cfb28d88c47eb251bc','source-manifest.json':'a6857429951a6510a4c85f83c560033390f8d3a17544cc69f48eec7854bae852'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33CurrentJonesSourceIff';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='0f17c0ee0d8758b70d0a3fd645a80a33748bf4c750b93fccc9acf0d176056721' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33CurrentSeedIff','DiophantineConsistency.SharingSeed33CurrentJones']
for x in ['∃ a : Fin 9 → V','ExecutableJones.expression (SharingSeed33.seed CurrentWindowCarry2011.ports) 0','∃ u : Fin 14 → V','InternalZero ObjectCurrentEquation2011.naturalExpression u','∃ w : Fin 33 → V','Fin.cons (1 : V) w','exists_congr fun w => (internalZero_iff (SharingSeed33.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)).symm','SharingSeed33CurrentJones.current_nine_iff (V := V)','Sign33CurrentSeedIff.seed_exists_iff_source (V := V)']:assert x in s
survey=(p/'provider_survey.py').read_text()
for h in ['a70978bcae7aba18f3b472554763f7222fed54e34f129a65cb9d9183bed36294','b522e615e253dc5f8d5b4f30a8f147578f060940e3e5b5c5dd78551ceb4cad87']:assert h in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'symbolic nine-variable/current-source iff in IΣ₁ models; no Lean replay'},indent=2,sort_keys=True))
