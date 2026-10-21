#!/usr/bin/env python3
"""Own static-audit runner. Runs only reviewed stdlib Python metadata/literal helpers."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');D=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/independent-audit';W=Path('/tmp/k215-literal-partition-v2-run1');W.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((D/'actual/endpoint/lean-source-closure.json').read_text());ad=json.loads((D/'actual/partition-v2/partition-adoption.json').read_text());inp=json.loads((D/'code/literal-inputs-v2.json').read_text())['inputs']
paths={Path(x['path'])for x in old['project_modules']}|{R/x['path']for x in ad['files']};assert len(paths)==204
paths|={R/p for p in inp};paths|={D/'code/literal_bindings_v2.py',D/'code/source_closure_v2.py',D/'code/literal-inputs-v2.json'}
before={str(p):sha(p)for p in sorted(paths)};jobs=[]
for name,script,out in [('literal','literal_bindings_v2.py','literal-bindings.json'),('closure','source_closure_v2.py','lean-source-closure.json')]:
 cmd=[sys.executable,'-B',str(D/'code'/script),'--repo',str(R),'--output',str(W/out)];t=time.monotonic()
 with (W/(name+'.stdout')).open('w')as stdout,(W/(name+'.stderr')).open('w')as stderr:
  p=subprocess.run(cmd,cwd=R,stdout=stdout,stderr=stderr,timeout=30)
 jobs.append({'name':name,'argv':cmd,'exit_code':p.returncode,'seconds':time.monotonic()-t,'stdout_sha256':sha(W/(name+'.stdout')),'stderr_sha256':sha(W/(name+'.stderr')),'output_sha256':sha(W/out)if(W/out).exists()else None})
 if p.returncode:break
after={str(p):sha(p)for p in sorted(paths)}
j={'status':'PASS'if len(jobs)==2 and all(x['exit_code']==0 for x in jobs)and before==after else'FAIL','scope':'Read-only literal and source-closure metadata checks; no Lean/Rocq compiler or machine execution','jobs':jobs,'before':before,'after':after,'all_inputs_unchanged':before==after};(W/'actual.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({'status':j['status'],'inputs':len(before),'seconds':[x['seconds']for x in jobs]}));assert j['status']=='PASS'
