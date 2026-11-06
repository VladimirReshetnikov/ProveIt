#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch03-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'b28abcf6bb39955eac6a4b937185719f050e930020a7bd02919bb95a592c7cca','provider_survey.py':'4be10fd0754f9b22f8d70ac548edb392d6b7934f314ed1aca57ff094c8a8660f','source-manifest.json':'172b84a0ea45e89306e7da18e22a92c5caec606bb573a6506c73141e33903599','src/DiophantineConsistency/Sign33ResidualBatch03.lean':'0ddc9592dd0c3a66fa0d62485479246928ec7d9f778306a58ad206d7bf3d9ad6'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33ResidualBatch03.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='0ddc9592dd0c3a66fa0d62485479246928ec7d9f778306a58ad206d7bf3d9ad6';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.SharingSign33Squares'];assert re.findall(r'^theorem (\w+)',s,re.M)==['row9_eval','row10_eval','row11_eval','two_cuts_and_norm_of_seed_zero'];assert len(re.findall(r'^#print axioms ',s,re.M))==4
result=d/'research/nine-sharing-sign33-residual-batch-plan/result.json';assert h(result)=='95244a5e2a3e94856144d5caae192b6d7cac454a4622aadf2eb9924e91fbf7a8';r=json.loads(result.read_text());assert [(x['gate'],x['ports'],x['kind']) for x in r['rows'][9:12]]==[('c2',[],'positive'),('Dc2',[],'positive'),('N1',[],'norm')]
for j in range(9,12):
 part=s.split(f'have hm{j} :',1)[1].split('exact List.mem_cons_self',1)[0];assert part.count('apply List.mem_cons_of_mem')==j
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'two cuts and one norm, uncompiled; no Lean replay'},sort_keys=True,indent=2))
