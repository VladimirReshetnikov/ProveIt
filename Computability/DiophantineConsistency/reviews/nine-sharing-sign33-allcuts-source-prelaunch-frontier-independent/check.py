#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-allcuts-source-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'9244ea4664afc46b2bab210f501d0d9d5a5f5e78c3860e5dbe6cd1d911b05409','provider_survey.py':'ef85b2d5dff0837e0b67fea006bbe8bc7bf43f6c9fc1a59e6a72fc6128343f55','source-manifest.json':'6153ceead8b9dc9386b9d736ac18d90b8f388dcc7ad9c19b839529371529da41','src/DiophantineConsistency/Sign33AllCutsSource.lean':'80e80a14f5eb8988912c42bd6a5da35cd0211db130284db69e1d6dcda988b7a2'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Sign33AllCutsSource.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='80e80a14f5eb8988912c42bd6a5da35cd0211db130284db69e1d6dcda988b7a2';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.Sign33LiftSourceValue','FreshModel106'];assert re.findall(r'^theorem (\w+)',s,re.M)==['allcuts_imply_source_zero']
for i in range(4):assert f'(hp{i} : ((p {i} : ℤ) : DiffRing V) = ι (ports {i}))' in s
for q in ['Sign33ResidualAssembly.AllCuts ports v','InternalZero (ObjectCurrentEquation2011.expressionAt p)','(Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j)) + 1','fin_cases j <;> assumption','rw [internalZero_iff, FreshModel106.evalRing_expressionAt65]','Sign33LiftSourceValue.allcuts_imply_value ports v hc']:assert q in s
model=Path('/tmp/normalized106-fresh-model-client-20261105/FreshModel106.lean').read_text();assert '(ObjectCurrentEquation2011.expressionAt p).evalRing v =' in model and 'Carrier65.value (fun j => (p j : R)) v' in model
survey=(p/'provider_survey.py').read_text();runner=(p/'run.py').read_text();assert "'Sign33LiftSourceValue'" in survey and "selected['FreshModel106']" in survey and 'selected direct dependency' in runner and 'selected direct guard' in runner
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'generic AllCuts to source syntax with four casts; no Lean replay'},indent=2,sort_keys=True))
