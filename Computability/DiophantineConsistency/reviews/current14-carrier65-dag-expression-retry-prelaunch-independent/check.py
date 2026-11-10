#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-dag-expression-retry-check';old=root/'research/current14-carrier65-dag-expression-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='95c725c6126baa3ce66bd8706854a329f1f81326224b86bb22abb52733c3b291' and sha(p/'source-manifest.json')=='98af7b39b92e6deb54ae8bce6c90ca3ecda4e6509d18a792ddb80066339507ef'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DAGExpression';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DAGValue','DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.WeightedExpressionDegree'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert s==a.replace('import DiophantineConsistency.CurrentEquationSyntax2011\n','import DiophantineConsistency.CurrentEquationSyntax2011\nimport DiophantineConsistency.WeightedExpressionDegree\n',1) and s!=a
weighted=root/'Lean/DiophantineConsistency/WeightedExpressionDegree.lean';assert all(z in weighted.read_text() for z in ('def evalRing','theorem evalRing_add','theorem evalRing_sub','theorem evalRing_mul','theorem evalRing_pow','theorem evalRing_var','theorem evalRing_constant','theorem evalRing_ofNat'))
for f in ('current14-carrier65-dag-expression-failure-independent','current14-carrier65-dag-value-congr-diagnostic-terminal-independent','current14-carrier65-dag-failure-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and '948b4e01db000ecf59395fc5555f51bf4b249f8922c40f40bbd6585b190b5772' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'direct-import retry; historical source/object pins, full Lean expression and external PDF binding separate'},indent=2))
