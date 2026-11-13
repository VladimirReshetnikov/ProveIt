#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-shift-partial-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='8fb18afee98a1dd5bd7400f285b770c9b8ee4bdd6d046a1b6bc6967fc18cfd82' and sha(p/'source-manifest.json')=='8e0b1ba323c1ffc197f6039a6b39cc78cc803e1cc0483591f2dac19a21f684b3'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectShiftPartial';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectShiftConstantLeaf'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(hpos : ∀ i : Fin n, extended nativeTheory ⊢!','(compiledOpen (.add (.var i) (.constant 1)) v) (compiledOpen (.var i) w)','splitNative v w (constantLeaf v w) hpos (negativeLeaf v w) e'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-shift-constant-leaf-terminal-independent','nine-sharing-sign14-positive74-object-shift-negative-leaf-terminal-independent','nine-sharing-sign14-positive74-object-shift-induction-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
b=json.loads((root/'research/nine-sharing-sign14-positive74-object-shift-constant-leaf-check/attempt01/state.json').read_text())
for mod,prior in [('Sign14Positive74ObjectShiftNegativeLeaf','nine-sharing-sign14-positive74-object-shift-negative-leaf-check'),('Sign14Positive74ObjectShiftInduction','nine-sharing-sign14-positive74-object-shift-induction-check')]:
 key=f'/tmp/nine-sharing-sign14-positive74-object-shift-constant-leaf-check-20261110/lib/DiophantineConsistency/{mod}.olean';q=Path(key); st=json.loads((root/'research'/prior/'attempt01/state.json').read_text());assert q.is_symlink() and str(q.resolve())==b['overlay_links'][key] and sha(q)==st['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed shift split induction with only positive-variable native leaf assumed; closure separate'},indent=2))
