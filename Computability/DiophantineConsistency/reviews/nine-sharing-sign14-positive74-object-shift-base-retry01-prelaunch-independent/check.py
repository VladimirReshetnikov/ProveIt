#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-shift-base-retry01-check';old=root/'research/nine-sharing-sign14-positive74-object-shift-base-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='8dc1a269d676275707af3bb67599bbfad7529b5f44847e5ec539573dc0ef6a99' and sha(p/'source-manifest.json')=='eabd919890e289ab0136342b5cb304efd25ce82e47cea4822343cc893fb1e446'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectShiftBase';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectMatrixGuard','DiophantineConsistency.IPRAAddRecursion'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert s==a.replace('simpa [m, IPRAAddRecursion.addZeroI, allClosure_succ]','simpa [m, zeroTerm, IPRAAddRecursion.addZeroI, allClosure_succ]') and s!=a
for f in ('nine-sharing-sign14-positive74-object-shift-base-failure-independent','nine-sharing-sign14-positive74-object-matrix-guard-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r and 'IPRAAddRecursion' in (p/'framework-survey.py').read_text()
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'zeroTerm-unfolding retry for variable-negative split and native zero-plus-zero'},indent=2))
