#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-shift-base-retry02-check';old=root/'research/nine-sharing-sign14-positive74-object-shift-base-retry01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='2f438ce1d118cb8f6ca691139b401a33c286788ae952ed52ac52bcca2a3fd081' and sha(p/'source-manifest.json')=='480cce828ce95dd7f4e106486d99f147372bf166e7efb49fad197b48787f0432'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectShiftBase';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectMatrixGuard','DiophantineConsistency.IPRAAddRecursion'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert s==a.replace('IPRAAddRecursion.addZeroI, allClosure_succ] using IPRAAddRecursion.add_zero_native','IPRAAddRecursion.addZeroI, allClosure_succ, Entailment.Provable] using IPRAAddRecursion.add_zero_native') and s!=a
for f in ('nine-sharing-sign14-positive74-object-shift-base-failure-independent','nine-sharing-sign14-positive74-object-shift-base-retry01-failure-independent','nine-sharing-sign14-positive74-object-matrix-guard-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r and 'IPRAAddRecursion' in (p/'framework-survey.py').read_text()
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'provability-unfolding retry for variable-negative split and native zero-plus-zero'},indent=2))
