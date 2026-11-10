#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-dag-check';draft=root/'research/current14-carrier65-dag-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='ca1363d832ce1b69da42688aa4bbd25251e13855e93be40a40718fd8d9e3322b' and sha(p/'source-manifest.json')=='71d6f8cca595c5926048fdab1ecafaeec4ff964719b801b5960182187222b292'
entries=json.loads((p/'source-manifest.json').read_text())['rows'];names=['ArithmeticDAG','Current14Carrier65DAGCore','Current14Carrier65DAGValue'];assert [e['module'].split('.')[-1] for e in entries]==names
for e,n in zip(entries,names):
 q=p/'src/DiophantineConsistency'/(n+'.lean');assert sha(q)==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',q.read_text(),re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',q.read_text())
assert (p/'src/DiophantineConsistency/ArithmeticDAG.lean').read_bytes()==(root/'Lean/DiophantineConsistency/ArithmeticDAG.lean').read_bytes()
s=(draft/'Current14Carrier65DAG.lean').read_text();cut=s.index('/-- This is the essential bridge');ending='\nend DiophantineConsistency.Current14Carrier65DAG\n';assert s.endswith(ending)
core=s[:cut].replace('import DiophantineConsistency.Carrier65\n','',1)+ending+'\n'+''.join('#print axioms DiophantineConsistency.Current14Carrier65DAG.'+x+'\n' for x in ('topological','operation_count','addition_count','subtraction_count','multiplication_count','live_operation_count','all_inputs','all_ports'))
value='import DiophantineConsistency.Current14Carrier65DAGCore\nimport DiophantineConsistency.Carrier65\n\nnamespace DiophantineConsistency.Current14Carrier65DAG\nopen ArithmeticDAG\n\n'+s[cut:]+'\n#print axioms DiophantineConsistency.Current14Carrier65DAG.value_eq_carrier\n'
assert (p/'src/DiophantineConsistency/Current14Carrier65DAGCore.lean').read_text()==core and (p/'src/DiophantineConsistency/Current14Carrier65DAGValue.lean').read_text()==value
for f in ('current14-carrier65-dag-draft-independent','nine-sharing-sign17-readable-current14-endpoint-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and 'direct producer' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'three proposed stages; semantic bridge and all Lean declarations untested; historical Carrier65 object point pin'},indent=2))
