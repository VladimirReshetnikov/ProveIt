#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-q-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'5423ea29e2da24360d3530c01872cdf7b26833cb3e244bfe5dd7773ea9d613a0','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'058c68b9c700afbfede003943a3c5267565e17166f5602be44d886366144125b','src/DiophantineConsistency/Sign33ForwardNormQ.lean':'faffcb8c15c734a4e2747196d1e1e3ae2587633b0ed1bc0cb67065c3d8b42f92'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Sign33ForwardNormQ.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='faffcb8c15c734a4e2747196d1e1e3ae2587633b0ed1bc0cb67065c3d8b42f92';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.SharingForward33','DiophantineConsistency.Sign33ResidualAssembly','FreshModel106']
for x in ['Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))','d.Q = 1','Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)','ι (v 23)*ι (v 23)-ι (v 25) = 1']:assert x in s
prior=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text();assert 'ι (v 23)*ι (v 23)-ι (v 25) = 1' in prior
core=(d/'Lean/DiophantineConsistency/Carrier65.lean').read_text();assert 'let Q := D ^ 2 - delta * c ^ 2' in core

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional forward Q norm only; no Lean replay'},indent=2,sort_keys=True))
