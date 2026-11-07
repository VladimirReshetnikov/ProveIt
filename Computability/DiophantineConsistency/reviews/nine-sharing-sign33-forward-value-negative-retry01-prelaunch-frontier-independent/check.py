#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-value-negative-retry01';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'aa3669c271c9371b196608dc12e5ba8b4224aee43ae5750b6e1f1d066cd39556','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'d295ee042789964bc4abb320c2fd1f0d36be5cf25d12ce06db3919de0292ad78','src/DiophantineConsistency/Sign33ForwardValueNegative.lean':'66d8a782a4dc98ef16d55e5d5e7a43400c6b91f1a0dc27aae480ce6a2a383ba1'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Sign33ForwardValueNegative.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='66d8a782a4dc98ef16d55e5d5e7a43400c6b91f1a0dc27aae480ce6a2a383ba1';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.SharingForward33','DiophantineConsistency.Sign33ResidualAssembly','FreshModel106']
assert re.findall(r'^theorem (\w+)',s,re.M)==['value_of_core','negative_of_core']
for x in ['Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))','ι inner = d.c * ι (u 6+1) - d.rank','ι value = d.V','ι negative = d.y*d.y-d.V*d.V','Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)']:assert x in s
prior=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text()
for term,stop in [('ι (v 30) =','∧'),('ι (v 33) =','∧')]:
 condition=s.split(term,1)[1].split(':= by',1)[0];batch=prior.split(term,1)[1].split(stop,1)[0];assert re.sub(r'\s+','',condition)==re.sub(r'\s+','',batch)
core=(d/'Lean/DiophantineConsistency/Carrier65.lean').read_text();assert 'let V := f ^ 2 * (c * T - rank) - c' in core and 'let y := v 12' in core

old=(d/'research/nine-sharing-sign33-forward-value-negative-check/src/DiophantineConsistency/Sign33ForwardValueNegative.lean').read_text();assert old.count('let v := Fin.cons')==2 and old.replace('let v := Fin.cons','let v : Fin 34 → V := Fin.cons')==s

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional forward value and negative cuts only; no Lean replay'},indent=2,sort_keys=True))
