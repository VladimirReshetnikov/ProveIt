#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-degree-expression-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='e67b2bc2f5f83765ece1732b855f6edd9361820b53c7ab9c1a3a8a3b6f868c74' and sha(p/'source-manifest.json')=='5e61d2a2173547d75450cd8bb614357fa83a7e80a140a83d83d85035257fa882'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DegreeExpression';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DegreeDirect','DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.WeightedExpressionDegree'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(ObjectCurrentEquation2011.expressionAt p).evalRing v','Carrier65.value (fun j => (p j : R)) v','(ObjectCurrentEquation2011.expressionAt p).toPolynomial = Carrier65.polynomial p','(hp : p 0 ≠ 0)','(ObjectCurrentEquation2011.expressionAt p).toPolynomial.totalDegree = 150','Current14Carrier65DegreeDirect.polynomial_exact p hp'):assert z in s
prior=(root/'research/current14-carrier65-dag-expression-retry-check/src/DiophantineConsistency/Current14Carrier65DAGExpression.lean').read_text();a=prior.split('  simp only [ObjectCurrentEquation2011.expressionAt',1)[1].split('\ntheorem value_eq_expression',1)[0].strip();b=s.split('  simp only [ObjectCurrentEquation2011.expressionAt',1)[1].split('\ntheorem expression_eq_polynomial',1)[0].strip();assert a==b
for f in ('current14-carrier65-degree-direct-retry-terminal-independent','current14-carrier65-dag-expression-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed current expression conditional exact degree p0 nonzero; PDF parsing separate'},indent=2))
