#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-diagonal-w-retry02-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='db5cd543806cbcf401bfc6ed538390ffbf583677ab1e601c27e042afdc0f61f1' and sha(p/'source-manifest.json')=='e05831c6a26f09af1af165e89bdc954f8fd9775e50e8628f5c062d86082d0bee'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DiagonalW';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14Carrier65DiagonalBinding'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(Polynomial.C K + Polynomial.X) *','Polynomial.C beta * Polynomial.X + 1 - Polynomial.X - Polynomial.X','Polynomial.X * (Polynomial.C beta * Polynomial.X)','Polynomial.C (-2) * Polynomial.X ^ 2','K * (beta - 2) + beta','Polynomial.C (K + 1)','(w beta K).coeff 2 = -2','(w beta K).natDegree = 2','(axisCore p).W = w (p 0) (p 1)','(axisCore p).W.natDegree = 2'):assert z in s
old=(root/'research/current14-carrier65-diagonal-w-retry-check/src/DiophantineConsistency/Current14Carrier65DiagonalW.lean').read_text()
assert old.replace('if_neg (by decide : (2 : ℕ) ≠ 0), add_zero]\n\ntheorem w_degree','if_neg (by decide : (2 : ℕ) ≠ 0), add_zero]\n  rfl\n\ntheorem w_degree')==s
for f in ('current14-carrier65-diagonal-w-failure-independent','current14-carrier65-diagonal-w-retry-failure-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-diagonal-binding-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed actual W diagonal coefficient -2 and degree 2 at arbitrary ports'},indent=2))
