#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-positive-to-shift-open-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='bb4b27584c6aab86ff4be50579fcbfd6283509784a8c1cb567b4ddc771751a41' and sha(p/'source-manifest.json')=='6feb69a6e57d5363440389ecc260428b510d189133abf7df4ee8e1a4b91a61a1'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectPositiveToShiftOpen';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectSuccGuard'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(Rew.emb (positiveNoZero e) 🡒 ∼(Rew.embSubsts v ▹ equalityMatrix (positiveShift e)))','let m : Semisentenceᵢ language 14 := guard 🡒 ∼equalityMatrix e','allInst (Λ := extended nativeTheory) (Rew.emb ▹ m) (succVec v)','hlogic ⨀ hs ⨀ succGuardOpen v','Entailment.contra (shiftForward v e)'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-succ-guard-retry01-terminal-independent','nine-sharing-sign14-positive74-object-shift-matrix-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
b=json.loads((root/'research/nine-sharing-sign14-positive74-object-succ-guard-retry01-check/attempt01/state.json').read_text());key='/tmp/nine-sharing-sign14-positive74-object-succ-guard-retry01-check-20261110/lib/DiophantineConsistency/Sign14Positive74ObjectShiftMatrix.olean';q=Path(key);st=json.loads((root/'research/nine-sharing-sign14-positive74-object-shift-matrix-check/attempt01/state.json').read_text());assert q.is_symlink() and str(q.resolve())==b['overlay_links'][key] and sha(q)==st['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed internal positive universal sentence implies shifted nonzero open matrix; reverse and closure separate'},indent=2))
