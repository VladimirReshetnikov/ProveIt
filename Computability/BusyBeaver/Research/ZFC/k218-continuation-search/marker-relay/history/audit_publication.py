"""Own metadata/source audit only; does not invoke candidate simulations."""
from pathlib import Path
import ast,json,gzip,hashlib,re
p=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay')
s=Path('/tmp/k217-row36-marker');checks=[]
def ck(v,name):
 if not v:raise AssertionError(name)
 checks.append(name)
def fun(path,name):return next(x for x in ast.parse(path.read_text()).body if isinstance(x,ast.FunctionDef)and x.name==name)
def tbl(path):return {tuple(map(int,r.split()[:2])):tuple(r.split()[2:])for r in path.read_text().splitlines()if r and not r.startswith('#')}
t=tbl(p/'../../candidate-k218/k218.native.tm');u=tbl(p/'relay217.native.tm')
ck(len(u)==434 and len({q for q,b in u})==217,'217/434 census')
ck({q for q,b in t}-{q for q,b in u}=={301},'only301 removed')
ck(len([k for k in u if t[k]!=u[k]])==11,'eleven retained changes')
ck(u==tbl(p/'history/relay-original-header.native.tm'),'two header formats same rows')
f=json.loads((p/'evidence/runtime-attempt/runtime/runtime.json').read_text());ck(f['status']=='NOT_PROVED'and f['prior_cases']==5932 and f['index']==4569,'root failure scope')
ck(json.loads((p/'evidence/runtime-attempt/execution.json').read_text())['returncode']==1,'root terminal failure')
h=json.loads(gzip.decompress((p/'history/actual-texts.json.gz').read_bytes()))
for e in h['files']:ck(hashlib.sha256(e['text'].encode()).hexdigest()==e['sha256'],'history '+e['path'])
ck(len(json.loads(gzip.decompress((p/'evidence/source-1m.trace.json.gz').read_bytes())))==1000000,'source trace count')
a=fun(s/'relay_root2m.py','run');b=fun(p/'diagnose.py','run')
old=next(x for x in a.body if isinstance(x,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='bound'for t in x.targets))
ck(ast.dump(old.value)==ast.dump(ast.parse('2000000 if blank else 30000',mode='eval').body),'exact old bound')
old.value=ast.parse('a.step_bound',mode='eval').body
ck(ast.dump(a)==ast.dump(b),'run AST unchanged except explicit bound')
ck(ast.dump(fun(s/'relay_root2m.py','frame'))==ast.dump(fun(p/'diagnose.py','frame')),'frame function unchanged')
for name in['resolve','inc','strip']:ck(ast.dump(fun(s/'source_continuation.py',name))==ast.dump(fun(p/'source_continue.py',name)),name+' unchanged')
for name in['README.md','proof.md']:
 for target in re.findall(r'\]\(([^)]+)\)',(p/name).read_text()):
  if target=='publication.json':continue
  ck((p/target).exists(),'link '+target)
result={'status':'OWN_SOURCE_AND_METADATA_AUDIT_PASS','role':'drop_contract is author; no independent authorship or candidate rerun claimed.','checks':checks,'candidate_invocation':False}
(p/'metadata-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(checks))
