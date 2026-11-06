#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch06-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'c3688eee6b5dcaf187b2bb0d5d6c676dc9c10b935029b07536fb63268e133c29','provider_survey.py':'8d5256d867e5a03030155cd9083d506c7fde1da959277956546db27e691d712e','source-manifest.json':'8980d88e9e8238a8fbcb767812fb57cccaaeedda9cf6880d43dce80eebee2e3a','src/DiophantineConsistency/Sign33ResidualBatch06.lean':'8224c869cf3ba236e16cdd8a070ced48a1e55426ecd5451b5b813fe96fe1239d'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33ResidualBatch06.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='8224c869cf3ba236e16cdd8a070ced48a1e55426ecd5451b5b813fe96fe1239d';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.SharingSign33Squares'];assert re.findall(r'^theorem (\w+)',s,re.M)==['row18_eval','row19_eval','row20_eval','three_cuts_of_seed_zero'];assert len(re.findall(r'^#print axioms ',s,re.M))==4
result=d/'research/nine-sharing-sign33-residual-batch-plan/result.json';assert h(result)=='95244a5e2a3e94856144d5caae192b6d7cac454a4622aadf2eb9924e91fbf7a8';r=json.loads(result.read_text());assert [(x['gate'],x['ports'],x['kind']) for x in r['rows'][18:21]]==[('V',[],'signed'),('normalized_S',[],'positive'),('normalized_S2',[],'positive')]
for j in range(18,21):
 part=s.split(f'have hm{j} :',1)[1].split('exact List.mem_cons_self',1)[0];assert part.count('apply List.mem_cons_of_mem')==j
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'three cuts, uncompiled; no Lean replay'},sort_keys=True,indent=2))
