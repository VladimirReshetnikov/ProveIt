#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-coordinate-probe-retry01-check';old=root/'research/nine-sharing-sign14-positive74-coordinate-probe-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='dab1b3e0342548ae01e13b53bfabc53cf611f77829480459463b4031610694a5' and sha(p/'source-manifest.json')=='233dab4a9549924e402942ec04e0fba4357735aab7a20067e00101b58ec9e3e0'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74CoordinateProbe';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74Expression'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
previous=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();h1='  have h1 : Fin.cases (1 : R) v (1 : Fin 15) = v 0 := by rfl\n';h2='  have h2 : Fin.cases (1 : R) v (2 : Fin 15) = v 1 := by rfl\n';expected=previous.replace('  simp [g00, oldB, Expr.evalRing, Fin.cons]',h1+'  simp [g00, oldB, Expr.evalRing, Fin.cons, h1]').replace('  simp [g01, g00, oldB, Expr.evalRing, Fin.cons]',h1+'  simp [g01, g00, oldB, Expr.evalRing, Fin.cons, h1]').replace('  simp [g26, g01, g00, oldB, Expr.evalRing, Fin.cons]',h1+h2+'  simp [g26, g01, g00, oldB, Expr.evalRing, Fin.cons, h1, h2]');assert s==expected
for f in ('nine-sharing-sign14-positive74-coordinate-probe-failure-independent','nine-sharing-sign14-positive74-syntax-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'three generic ring node identities only; row/model/file proof separate'},indent=2))
