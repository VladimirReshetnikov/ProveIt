#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-syntax-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d6b61c8da269c3960038dca7c68435ebfa77b9f8a98cfe316a697ee2ddc2f85f' and sha(p/'source-manifest.json')=='cef148ecfa32b57389fc33eee1b516a37a518420c809943cb4ea5f8714dd527c'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==10
for i,e in enumerate(rows):
 n=f'Sign14Positive74Nodes{i:02}' if i<9 else 'Sign14Positive74Expression';dep='Sign14Optimized86Expression' if i==0 else f'Sign14Positive74Nodes{i-1:02}';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.'+dep] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for f in ('nine-sharing-sign14-positive74-candidate-independent','nine-sharing-sign14-positive74-lean-draft-independent','nine-sharing-sign14-86gate-expression-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
base=Path('/tmp/nine-sharing-sign14-86gate-expression-check-20261110');st=json.loads((root/'research/nine-sharing-sign14-86gate-expression-check/attempt01/state.json').read_text());assert st['status']=='PASS';row,=st['rows'];obj=base/'lib/DiophantineConsistency/Sign14Optimized86Expression.olean';assert sha(obj)==row['object_sha256']
for mod,d in row['dependencies'].items():
 if mod=='Init':continue
 z=base/'lib'/(mod.replace('.','/')+'.olean');assert z.is_file() and str(z.resolve())==d['realpath'] and sha(z)==d['sha256'] and st['overlay_links'][str(z)]==d['realpath']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':10,'scope':'proposed positive-input symbolic syntax only; no Lean coordinate shift, model bridge, JSON or PDF theorem'},indent=2))
