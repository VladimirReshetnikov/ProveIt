#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-seed-iff-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'feeb784f360658efa58aa2dba03a8429844ad3ac6832d330e4618e10a525970c','provider_survey.py':'a14991fa08419175d02224ac11f2f591786251516ed9ddd7a0edc52c41cf0263','source-manifest.json':'faa18169a1917f25f23c05fc699e14a0ca863c6cba6df59d9e96fbd1ce78697a'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33CurrentSeedIff';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='e1f8fe053dcb1d1cad7caa1f29ec21e0842060ad6d940501952b971acebf7b62' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33CurrentSourceSeedCastFree','DiophantineConsistency.Sign33CurrentSeedSourceRetry']
for x in ['∃ w : Fin 33 → V','Fin.cons (1 : V) w','∃ u : Fin 14 → V','InternalZero ObjectCurrentEquation2011.naturalExpression u','Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j)','internalZero_positiveShift ObjectCurrentEquation2011.expression u).mpr','current_seed_implies_source v hw','current_source_implies_seed u hu']:assert x in s
rev=(d/'research/nine-sharing-sign33-seed-current-source-retry01/src/DiophantineConsistency/Sign33CurrentSeedSourceRetry.lean').read_text();assert 'Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j)) + 1' in rev
survey=(p/'provider_survey.py').read_text();assert 'c91c2cf8a14bd68341d5c80c270c8ee8c4afae9ead9e5dccf242a8d346368140' in survey and 'Sign33CurrentSeedSourceRetry' in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'existential 33-seed/current natural-source equivalence in IΣ₁ models; no Lean replay'},indent=2,sort_keys=True))
