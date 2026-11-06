#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch05-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'8d66591b50f0adb6189b70dea534745c8e176c147366b1695bd57f41c34d6b40','provider_survey.py':'4139d7bd877acce57b04561a2a7dd087a64dc6b52f019d8b52bce2e1ed1c726e','source-manifest.json':'40e0e7551e4fbc45229253f038f96c03b8fb1f12bddc4c13fe609207d8b55a32','src/DiophantineConsistency/Sign33ResidualBatch05.lean':'0935fca1965fc7d0d6c45337404a70a8863cd1df080f1f1a8527cf4a88bef5ce'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33ResidualBatch05.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='0935fca1965fc7d0d6c45337404a70a8863cd1df080f1f1a8527cf4a88bef5ce';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.SharingSign33Squares'];assert re.findall(r'^theorem (\w+)',s,re.M)==['row15_eval','row16_eval','row17_eval','transport_and_cuts_of_seed_zero'];assert len(re.findall(r'^#print axioms ',s,re.M))==4
result=d/'research/nine-sharing-sign33-residual-batch-plan/result.json';assert h(result)=='95244a5e2a3e94856144d5caae192b6d7cac454a4622aadf2eb9924e91fbf7a8';r=json.loads(result.read_text());assert [(x['gate'],x['ports'],x['kind']) for x in r['rows'][15:18]]==[('Nt',['K0','beta'],'norm'),('f2',[],'positive'),('cTminusR',['MC','MF','beta'],'signed')]
for j in range(15,18):
 part=s.split(f'have hm{j} :',1)[1].split('exact List.mem_cons_self',1)[0];assert part.count('apply List.mem_cons_of_mem')==j
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'transport norm and two cuts, uncompiled; no Lean replay'},sort_keys=True,indent=2))
