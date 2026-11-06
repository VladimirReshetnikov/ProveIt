#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-five-norms-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'c943e5e71feb8566739461075bd62019842d2b0ceae07e7c616e38ad3551289a','provider_survey.py':'8a60bb2a886f04be16d80361315cdbb4975bf7ed52f524d61c65234e6a1e1b92','source-manifest.json':'8f8d9344fddfdfa6fde39f8c807035b289008410bb052ef06a0a514c81584432'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==6
hashes=['d629f153b86320587ad35c73d4368dc2ffcc6a2e24879ca537216d4f1fde861e','26985d59f6ce952d9724a8f689e4c383cd28b33ebe6bd820c02f54347f2bd7db','47ea48b2aa24088a965c1355b9b44ee31fc109931c92d6943add2513e7188921','a871f247eec36a50ee254bec5cf19f6a78ae3b9da0aa36812685060f5e8ed87c','73066e189da0d2c6582f5b6a9ee79313b50110b2845ca476d6f9a8b338564995','0542f3eadb5f017228289617e8f645e4a7fbdb8308b7dfe7de2ddeda8efbf434']
fields=['batch04.2.2','batch03.2.2','batch07.2.1','batch05.1','batch07.2.2'];targets=[61,44,78,66,80]
for i,row in enumerate(rows):
 n=('Sign33LiftNorm'+str(i)) if i<5 else 'Sign33LiftFiveNorms';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==hashes[i];assert re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']
 if i<5:
  assert row['imports']==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert 'have h := hc.'+fields[i] in s and f'pairValue ι (a {targets[i]}) = '+('pairValue ι (a 36)' if i==4 else '1') in s and 'Sign33ResidualAssembly.AllCuts ports v' in s
 else:
  assert row['imports']==['DiophantineConsistency.Sign33LiftNorm'+str(j) for j in range(5)];assert 'NormAssignment38.fiveNorms ι ports (Sign33Lift38.lift v)' in s;assert re.findall(r'Sign33LiftNorm(\d).norm ports v hc',s)==list('01234')
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text().split('def fiveNorms',1)[1];assert re.findall(r'pairValue embed \(v (\d+)\)',g)[:6]==['61','44','78','66','80','36']
assembly=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text();assert 'ι (v 22)*ι (v 28)-ι (v 32) = ι (v 22)' in assembly and '(ι (v 13)+1)*(ι (v 13)+1)-ι (v 32)*ι (v 33) = 1' in assembly
runner=(p/'run.py').read_text();assert "for mod in imports:" in runner and "local producer binding" in runner and "selected direct dependency" in runner
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==6
print(json.dumps({'status':'PASS','preflight':o,'scope':'five norm source projections and point-provider review; no Lean replay'},indent=2,sort_keys=True))
