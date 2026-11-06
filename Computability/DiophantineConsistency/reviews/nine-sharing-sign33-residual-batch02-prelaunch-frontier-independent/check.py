#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch02-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'70ace19d46ddf7a5d4b4562e39326e6a7f00dcb120a75ab02603f3c6136cc90c','provider_survey.py':'7656a777f95cedf7b4c4ab577577e2122f3d3a25b3630c7354ff2b64ce118c43','source-manifest.json':'dc990ae70c7e8a29b748851d75df1c3236b2529822d06af8693d3ad4e1d43714','src/DiophantineConsistency/Sign33ResidualBatch02.lean':'dddf446dd66f4467cccc5fbe0fd46b57c54be9b4b7e663ebd94e5b15dfb6c5da'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33ResidualBatch02.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='dddf446dd66f4467cccc5fbe0fd46b57c54be9b4b7e663ebd94e5b15dfb6c5da';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.SharingSign33Squares'];assert re.findall(r'^theorem (\w+)',s,re.M)==['row6_eval','row7_eval','row8_eval','three_cuts_of_seed_zero'];assert len(re.findall(r'^#print axioms ',s,re.M))==4
result=d/'research/nine-sharing-sign33-residual-batch-plan/result.json';assert h(result)=='95244a5e2a3e94856144d5caae192b6d7cac454a4622aadf2eb9924e91fbf7a8';r=json.loads(result.read_text());assert [(x['gate'],x['ports']) for x in r['rows'][6:9]]==[('ell',[]),('Delta',[]),('main_root',[])]
for j in range(6,9):
 part=s.split(f'have hm{j} :',1)[1].split('exact List.mem_cons_self',1)[0];assert part.count('apply List.mem_cons_of_mem')==j
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'three uncompiled same-valuation cuts; no Lean replay'},sort_keys=True,indent=2))
