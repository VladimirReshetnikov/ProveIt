#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch00-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'0202da394894c3b896a273d7ec72bb324f2cf78ebae036507e307dedcd0feb09','provider_survey.py':'d5460b09e41b995b53aa13cc36669f15bb0b8c5b3b3380159fd32f491aabea2f','source-manifest.json':'4f34560c23918c083bd53911be1842ffe41bbe40c78dd96166b04a7d1b051fe5','src/DiophantineConsistency/Sign33ResidualBatch00.lean':'8b0ae5b586f534856b90b8de1afe334df3819e4cf676f3e693d358bd50463ece'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33ResidualBatch00.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='8b0ae5b586f534856b90b8de1afe334df3819e4cf676f3e693d358bd50463ece';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33FirstCut','DiophantineConsistency.SharingSign33Squares'];assert re.findall(r'^theorem (\w+)',s,re.M)==['row1_eval','row2_eval','three_cuts_of_seed_zero'];assert len(re.findall(r'^#print axioms ',s,re.M))==3
result=d/'research/nine-sharing-sign33-residual-batch-plan/result.json';assert h(result)=='95244a5e2a3e94856144d5caae192b6d7cac454a4622aadf2eb9924e91fbf7a8';r=json.loads(result.read_text());assert [(x['gate'],x['ports']) for x in r['rows'][:3]]==[('q2',['beta']),('q3',['beta']),('X',['beta'])]
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'three uncompiled same-valuation cuts; no Lean replay'},sort_keys=True,indent=2))
