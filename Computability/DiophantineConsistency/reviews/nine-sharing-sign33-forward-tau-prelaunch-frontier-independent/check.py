#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-tau-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'0ed30ae5b5bb23552fd9a5edf3a43ad269b0666528238ef1140859041d373ec9','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'89add8034d450607642b0406af1a3d90d2dfb13674d7a8a8a2e73cbdf1ce1022','src/DiophantineConsistency/Sign33ForwardTau.lean':'12d890f7c8e2aeed18c6ae4419c31546b2d6ce3085aa5979c67acf428c970424'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Sign33ForwardTau.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='12d890f7c8e2aeed18c6ae4419c31546b2d6ce3085aa5979c67acf428c970424';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.SharingForward33','DiophantineConsistency.Sign33ResidualAssembly','FreshModel106']
for x in ['Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))','ι gap = (d.q-1)*(d.q-ι (u 1+1))+ι (u 2+1)','ι tau = d.tau','Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)','ι (v 27) = ((ι (v 19)*(ι (v 10)+1)+((ι (v 11)+1)+(ι (v 12)+1)))+ι (v 26))-','(ι (v 26)*ι (v 15)+(ι (ports 2)+Sign33ResidualBatch04.q ports v*ι (ports 3))*(ι (v 1)+1))']:assert x in s
prior=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text();condition=s.split('ι (v 27) =',1)[1].split(':= by',1)[0];batch=prior.split('ι (v 27) =',1)[1].split('∧',1)[0];assert re.sub(r'\s+','',condition)==re.sub(r'\s+','',batch)
core=(d/'Lean/DiophantineConsistency/Carrier65.lean').read_text();assert 'let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) + (p 2 + q * p 3) * J' in core and 'let tau := E * n + k - rank' in core

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional forward tau cut only; no Lean replay'},indent=2,sort_keys=True))
