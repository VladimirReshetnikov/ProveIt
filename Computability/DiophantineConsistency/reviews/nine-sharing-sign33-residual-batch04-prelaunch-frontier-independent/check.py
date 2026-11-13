#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch04-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'a858642fba373c92ba4e77fa66a0218ff208188239d012bd0124dbeb6f5e8677','provider_survey.py':'d89ac5359570127143b35ccf539adb81df647c8f188427f29662dcf5d3ece73a','source-manifest.json':'022e45fea47e86d5d747129497464af14bf70d0170343657bc0adcde161ed59a','src/DiophantineConsistency/Sign33ResidualBatch04.lean':'2497af05c79a7c5c586b183bd58fca389728f8736f4ef39dc7524ce6c2d3d10a'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33ResidualBatch04.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='2497af05c79a7c5c586b183bd58fca389728f8736f4ef39dc7524ce6c2d3d10a';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.SharingSign33Squares'];assert re.findall(r'^theorem (\w+)',s,re.M)==['row12_eval','row13_eval','row14_eval','signed_cuts_and_norm_of_seed_zero'];assert len(re.findall(r'^#print axioms ',s,re.M))==4
result=d/'research/nine-sharing-sign33-residual-batch-plan/result.json';assert h(result)=='95244a5e2a3e94856144d5caae192b6d7cac454a4622aadf2eb9924e91fbf7a8';r=json.loads(result.read_text());assert [(x['gate'],x['ports'],x['kind']) for x in r['rows'][12:15]]==[('gap',['beta'],'signed'),('tau',['MC','MF','beta'],'signed'),('N0',[],'norm')]
for j in range(12,15):
 part=s.split(f'have hm{j} :',1)[1].split('exact List.mem_cons_self',1)[0];assert part.count('apply List.mem_cons_of_mem')==j
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'two signed cuts and one norm, uncompiled; no Lean replay'},sort_keys=True,indent=2))
