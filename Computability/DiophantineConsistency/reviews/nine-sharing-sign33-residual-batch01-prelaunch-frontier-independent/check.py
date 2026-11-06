#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch01-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'afbb3815899082725dcf29006b393607e928ee34170cec493be4bc18d4a5bea1','provider_survey.py':'8f5f62e24aed20061f7d8bd77f754b32b6e40d58d4ae6de1437f8af22249b07b','source-manifest.json':'191820415c665148a3f2c54eb7426832b6617641624c097534e14e84ea919ee2','src/DiophantineConsistency/Sign33ResidualBatch01.lean':'c5a5b2664f56d3b07307dd9e55155feda19e793f76cd3ecdd4ec02feb7e5d8f5'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33ResidualBatch01.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='c5a5b2664f56d3b07307dd9e55155feda19e793f76cd3ecdd4ec02feb7e5d8f5';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.SharingSign33Squares'];assert re.findall(r'^theorem (\w+)',s,re.M)==['row3_eval','row4_eval','row5_eval','three_cuts_of_seed_zero'];assert len(re.findall(r'^#print axioms ',s,re.M))==4
result=d/'research/nine-sharing-sign33-residual-batch-plan/result.json';assert h(result)=='95244a5e2a3e94856144d5caae192b6d7cac454a4622aadf2eb9924e91fbf7a8';r=json.loads(result.read_text());assert [(x['gate'],x['ports']) for x in r['rows'][3:6]]==[('Y',[]),('E',[]),('kY',[])]
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'three uncompiled same-valuation cuts; no Lean replay'},sort_keys=True,indent=2))
