#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-shift-matrix-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d909b865b34cc8ee3bec644ac773e534e170e4d66710ef71643bb726568abad4' and sha(p/'source-manifest.json')=='5ad765fa518d4da6a2cc3d87c9e0dee9609716128305cf162e4667205aac45c8'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectShiftMatrix';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectEqualityTransport'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(Rew.embSubsts v ▹ equalityMatrix e)','eqAt (compiledOpen e.splitNatural.1 v) (compiledOpen e.splitNatural.2 v)','((Rew.embSubsts v ▹ equalityMatrix (positiveShift e)) 🡒','(Rew.embSubsts (succVec v) ▹ equalityMatrix e))','exact equalityForward _ _ _ _ h.1 h.2','exact equalityBackward _ _ _ _ h.1 h.2'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-equality-transport-retry01-terminal-independent','nine-sharing-sign14-positive74-object-shift-full-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
b=json.loads((root/'research/nine-sharing-sign14-positive74-object-equality-transport-retry01-check/attempt01/state.json').read_text());key='/tmp/nine-sharing-sign14-positive74-object-equality-transport-retry01-check-20261110/lib/DiophantineConsistency/Sign14Positive74ObjectShiftFull.olean';q=Path(key);st=json.loads((root/'research/nine-sharing-sign14-positive74-object-shift-full-check/attempt01/state.json').read_text());assert q.is_symlink() and str(q.resolve())==b['overlay_links'][key] and sha(q)==st['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed both native shifted equality-matrix implications at successor assignment; quantified closure separate'},indent=2))
