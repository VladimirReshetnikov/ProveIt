#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-dag-value-retry-check';old=root/'research/current14-carrier65-dag-check';repo=root.parents[1];sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='2f7322112d0094711170fb1ea52861b16047df2285f615e3528a6c3a124c6361' and sha(p/'source-manifest.json')=='9946e96d72bad8f312f63376eb568acb68e1f123eedc05a8d0f7514543baea61'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DAGValue';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DAGCore','DiophantineConsistency.Carrier65'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
a=a.replace('simp only [value, output, nodes, run, Node.eval, List.getD,\n    List.append, Carrier65.value, Carrier65.core, pow_succ, pow_zero,','simp only [value, output, nodes, run, Node.eval, List.nil_append,\n    List.cons_append, List.getD_cons_zero, List.getD_cons_succ,\n    Carrier65.value, Carrier65.core, pow_succ, pow_zero,');assert s==a
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-dag-failure-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and 'failed final object absent' in r and 'successful children only' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'semantic retry only; two successful children of failed parent, historical Carrier65 object point pin'},indent=2))
