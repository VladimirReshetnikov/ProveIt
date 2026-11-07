#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-jones-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'04c48b9bc0db839d9e2c08e01335082ec764dabca1622467fea59a3cf215ed93','provider_survey.py':'459a92262e2041363b1e6bf1a3aa930d2ce05c3701f039ad19032a1f938038b6','source-manifest.json':'2c126c3a53d14ff95eb7e59cf896d04ddf3da773c59fb81398ea1044e0acdce3'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='SharingSeed33CurrentJones';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='f41fe843a3c5fb5a5410756d3ceeac26a1a2e4f9121053615a4b0543671da280' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+x for x in ['SharingSeed33Degree','SharingSeed33Normalize','SharingSeed38CurrentJones']]
for x in ['SharingSeed38CurrentJones.current_beta_positive','SharingSeed33.seed_degree _','SharingSeed33.seed_normalized _ current_beta_positive 1','ExecutableJones.expression (SharingSeed33.seed CurrentWindowCarry2011.ports) 0','∃ a : Fin 9 → V','∃ w : Fin 33 → V','Fin.cons (1 : V) w','NineFreshJones.nine_iff _ current_degree current_normalized']:assert x in s
assert re.findall(r'^theorem (\w+)',s,re.M)==['current_beta_positive','current_degree','current_normalized','current_nine_iff'] and s.count('#print axioms ')==4
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'33-seed Jones nine-variable correspondence proposal; no Lean replay'},indent=2,sort_keys=True))
