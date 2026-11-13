#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-dag-expression-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='7f7ab5629dbe1679ddd0eea76e9af4b72a54924535486c10bdd88d24aac11d4b' and sha(p/'source-manifest.json')=='867101a66d2a5166f0606dc61ddde68609cd6b4a8be64124ef25ad1551c8bdd9'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DAGExpression';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DAGValue','DiophantineConsistency.CurrentEquationSyntax2011'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
orig=(root/'Lean/DiophantineConsistency/ObjectCurrentEquation2011.lean').read_text().split('theorem evalRing_expressionAt',1)[1].split('\ntheorem eval_expressionAt',1)[0];new=s.split('theorem expression_eval_eq_carrier',1)[1].split('\ntheorem value_eq_expression',1)[0];assert ''.join(orig.split())==''.join(new.replace('ObjectCurrentEquation2011.expressionAt','expressionAt').split())
for z in ('value nodes output (fun j => (p j : R)) v','(ObjectCurrentEquation2011.expressionAt p).evalRing v','Topological nodes ∧ operationCount nodes = 65','liveOperationCount nodes output = 65','kindCount nodes 3 = 16 ∧ kindCount nodes 4 = 12','kindCount nodes 5 = 37','value_eq_carrier _ _','(expression_eval_eq_carrier p v).symm'):assert z in s
for f in ('current14-carrier65-dag-value-congr-diagnostic-terminal-independent','current14-carrier65-dag-failure-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and 'historical expression syntax point pin' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed graph/current Lean expression composition; historical point objects and external PDF boundary'},indent=2))
