#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-value-negative-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'36561f62b22342e624b12805fdc3265416b7370d2f7d437903ff523606417310','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'cdd005adf21f9d8dbec92a8237df84f4745c0b19e2349f3a24cfb63f94405229','src/DiophantineConsistency/Sign33ForwardValueNegative.lean':'07908bd4b4850700f5fda96103abddc45deb55f5804404b38e2c673debd97fe9'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Sign33ForwardValueNegative.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='07908bd4b4850700f5fda96103abddc45deb55f5804404b38e2c673debd97fe9';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.SharingForward33','DiophantineConsistency.Sign33ResidualAssembly','FreshModel106']
assert re.findall(r'^theorem (\w+)',s,re.M)==['value_of_core','negative_of_core']
for x in ['Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))','ι inner = d.c * ι (u 6+1) - d.rank','ι value = d.V','ι negative = d.y*d.y-d.V*d.V','Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)']:assert x in s
prior=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text()
for term,stop in [('ι (v 30) =','∧'),('ι (v 33) =','∧')]:
 condition=s.split(term,1)[1].split(':= by',1)[0];batch=prior.split(term,1)[1].split(stop,1)[0];assert re.sub(r'\s+','',condition)==re.sub(r'\s+','',batch)
core=(d/'Lean/DiophantineConsistency/Carrier65.lean').read_text();assert 'let V := f ^ 2 * (c * T - rank) - c' in core and 'let y := v 12' in core

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional forward value and negative cuts only; no Lean replay'},indent=2,sort_keys=True))
