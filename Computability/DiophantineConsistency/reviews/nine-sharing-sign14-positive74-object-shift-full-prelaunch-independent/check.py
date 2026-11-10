#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-shift-full-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='b7820ee4392cbc6b276719d08baedb599fff659bef1f4ab5b6d682c0a4e90c81' and sha(p/'source-manifest.json')=='b4bfc47fff80b666a9e9500017c98b081f753f63115ba26b34af3b4a0ec0c1b9'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectShiftFull';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectShiftPositiveLeaf'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(v : Fin n → Term language ℕ) (e : Expr (Fin n))','(compiledOpen (positiveShift e).splitNatural.1 v) (compiledOpen e.splitNatural.1 (succVec v))','(compiledOpen (positiveShift e).splitNatural.2 v) (compiledOpen e.splitNatural.2 (succVec v))','partialSplitNative v (succVec v) (positiveLeaf v) e'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-shift-positive-leaf-terminal-independent','nine-sharing-sign14-positive74-object-shift-partial-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
b=json.loads((root/'research/nine-sharing-sign14-positive74-object-shift-positive-leaf-check/attempt01/state.json').read_text());key='/tmp/nine-sharing-sign14-positive74-object-shift-positive-leaf-check-20261110/lib/DiophantineConsistency/Sign14Positive74ObjectShiftPartial.olean';q=Path(key);st=json.loads((root/'research/nine-sharing-sign14-positive74-object-shift-partial-check/attempt01/state.json').read_text());assert q.is_symlink() and str(q.resolve())==b['overlay_links'][key] and sha(q)==st['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed native both split-part shift equalities under successor assignment without leaf hypotheses; matrix and closure separate'},indent=2))
