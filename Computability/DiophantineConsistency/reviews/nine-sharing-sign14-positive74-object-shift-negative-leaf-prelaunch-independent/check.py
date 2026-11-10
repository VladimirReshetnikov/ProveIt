#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-shift-negative-leaf-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='082a965b5872099925b3ff5ed1194d68cd8177ee20be5d0984604f44cd579d9a' and sha(p/'source-manifest.json')=='9a58aac6fce0473c04c466560ef5898ebd374da76a3b48e34a6b2238e0bf96b3'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectShiftNegativeLeaf';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectCompilerLeaves'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(compiledOpen (.add (.constant 0) (.constant 0)) v) (compiledOpen (.constant 0) w)','simpa only [compiled_add, compiled_zero] using zeroAddZero'): assert z in s
for f in ('nine-sharing-sign14-positive74-object-compiler-leaves-retry01-terminal-independent','nine-sharing-sign14-positive74-object-shift-base-retry02-terminal-independent','nine-sharing-sign14-positive74-object-compiler-ops-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
b=json.loads((root/'research/nine-sharing-sign14-positive74-object-compiler-leaves-retry01-check/attempt01/state.json').read_text())
for mod,prior in [('Sign14Positive74ObjectShiftBase','nine-sharing-sign14-positive74-object-shift-base-retry02-check'),('Sign14Positive74ObjectCompilerOps','nine-sharing-sign14-positive74-object-compiler-ops-retry01-check')]:
 key=f'/tmp/nine-sharing-sign14-positive74-object-compiler-leaves-retry01-check-20261110/lib/DiophantineConsistency/{mod}.olean'; q=Path(key); state=json.loads((root/'research'/prior/'attempt01/state.json').read_text());assert q.is_symlink() and str(q.resolve())==b['overlay_links'][key] and sha(q)==state['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed native negative variable leaf zero-plus-zero proof; constant and positive leaves and sentence closure separate'},indent=2))
