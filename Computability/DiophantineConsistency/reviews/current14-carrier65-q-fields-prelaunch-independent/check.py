#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-q-fields-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='c34c383a0ab9fc47b9c3ad24a8b29a0d197cd0d3fc93446f98a362046bda7aa2' and sha(p/'source-manifest.json')=='b33f3e57bb620592825df6d5329e4c7260787a32ead4bf2187c43ec19ddc669e'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65QFields';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65QInputs','DiophantineConsistency.Carrier65'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for name,val in [('X',2),('c',5),('a',6),('H',6)]:
 assert f'theorem {name}_eval' in s and f').{name} := by' in s and f'theorem core_{name}_degree' in s and f').{name}).totalDegree ≤ {val}' in s and f'rw [{name}_weight, {name}_eval] at h' in s
for z in ('Expr.degree_evalRing_le','MvPolynomial.totalDegree_X','(fun j => (p j : MvPolynomial (Fin 14) ℤ)) MvPolynomial.X'):assert z in s
for f in ('current14-carrier65-q-inputs-retry-terminal-independent','current14-carrier65-q-inputs-failure-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and '10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed actual Carrier65 X/c/a/H degree bounds; Q and whole degree separate'},indent=2))
