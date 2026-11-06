#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch07-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'7a5fb13b729af2f66947ea27279e49e3910cddd80c7815bdfc5e91b4eb287311','provider_survey.py':'231120c0b270845dd4d83986136d8d434945c5b9bc388bb2ec9ba98385503baa','source-manifest.json':'6f364865fe07e2326d9e98ed01b3708f3fb6c9adfc998bfa5d91c74efbc0e10c','src/DiophantineConsistency/Sign33ResidualBatch07.lean':'a885cf06bee543a48505664621cd553f2a30bd868aa563893c26f4b9c34af45d'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33ResidualBatch07.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='a885cf06bee543a48505664621cd553f2a30bd868aa563893c26f4b9c34af45d';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.SharingSign33Squares'];assert re.findall(r'^theorem (\w+)',s,re.M)==['row21_eval','row22_eval','row23_eval','cut_and_norms_of_seed_zero'];assert len(re.findall(r'^#print axioms ',s,re.M))==4
result=d/'research/nine-sharing-sign33-residual-batch-plan/result.json';assert h(result)=='95244a5e2a3e94856144d5caae192b6d7cac454a4622aadf2eb9924e91fbf7a8';r=json.loads(result.read_text());assert [(x['gate'],x['ports'],x['kind']) for x in r['rows'][21:24]]==[('V2minusY2',[],'signed'),('Na',[],'norm'),('scaled_Ns',[],'norm')]
for j in range(21,24):
 part=s.split(f'have hm{j} :',1)[1].split('exact List.mem_cons_self',1)[0];assert part.count('apply List.mem_cons_of_mem')==j
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'negative-orientation cut and two norms, uncompiled; no Lean replay'},sort_keys=True,indent=2))
