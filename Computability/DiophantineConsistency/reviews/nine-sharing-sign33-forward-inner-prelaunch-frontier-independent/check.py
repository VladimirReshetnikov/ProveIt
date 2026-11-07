#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-inner-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'1ace7923bfaa9693f58f8c453cd0f6d941c2669473b69e887d851114ca813b8d','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'2b7f7452f8d92f5086b914c4c69dfe550634f44ba7b904425434462722ddc1dd','src/DiophantineConsistency/Sign33ForwardInner.lean':'82ccb5424f22e331daf55f08abaaa23825637abb0b7209eed7b6e50322263ee0'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Sign33ForwardInner.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='82ccb5424f22e331daf55f08abaaa23825637abb0b7209eed7b6e50322263ee0';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.SharingForward33','DiophantineConsistency.Sign33ResidualAssembly','FreshModel106']
for x in ['Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))','ι gap = (d.q-1)*(d.q-ι (u 1+1))+ι (u 2+1)','ι inner = d.c * ι (u 6+1) - d.rank','Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)','ι (v 29) = ((ι (v 20)+(ι (v 11)+1))*(ι (v 7)+1)+ι (v 26))-','(ι (v 26)*ι (v 15)+(ι (ports 2)+Sign33ResidualBatch05.q ports v*ι (ports 3))*(ι (v 1)+1))']:assert x in s
prior=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text();condition=s.split('ι (v 29) =',1)[1].split(':= by',1)[0];batch=prior.split('ι (v 29) =',1)[1].split('  batch06 :',1)[0];assert re.sub(r'\s+','',condition)==re.sub(r'\s+','',batch)
core=(d/'Lean/DiophantineConsistency/Carrier65.lean').read_text();assert 'let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) + (p 2 + q * p 3) * J' in core and 'let c := k * Y + eta' in core

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional forward inner cut only; no Lean replay'},indent=2,sort_keys=True))
