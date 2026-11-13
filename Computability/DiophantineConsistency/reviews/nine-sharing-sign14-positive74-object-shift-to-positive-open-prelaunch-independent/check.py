#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-shift-to-positive-open-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='9f6cc643c173ae3ae7fdc451c06f7389c1c89e42dd762a8fa920f3979e702955' and sha(p/'source-manifest.json')=='cc2445a22e3394a39bd87926d710ba6f6e74e93dc8f90fab7d91949eee9c9831'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectShiftToPositiveOpen';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectPositiveToShiftOpen'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(Rewriting.emb (nativeNoZero (positiveShift e)) 🡒','((Rew.embSubsts v ▹ guard) 🡒 ∼(Rew.embSubsts v ▹ equalityMatrix e))','fun i => pred (v i)','allInst (Λ := extended nativeTheory) (Rew.emb ▹ m) (predVec v)','succVec (predVec v) = predSuccVec v','shiftBackward (predVec v) e','Entailment.contra hb','Entailment.C_swap (guardedContrapositive e v)'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-positive-to-shift-open-retry02-terminal-independent','nine-sharing-sign14-positive74-object-shift-matrix-terminal-independent','nine-sharing-sign14-positive74-object-matrix-guard-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
b=json.loads((root/'research/nine-sharing-sign14-positive74-object-positive-to-shift-open-retry02-check/attempt01/state.json').read_text())
for mod,prior in [('Sign14Positive74ObjectShiftMatrix','nine-sharing-sign14-positive74-object-shift-matrix-check'),('Sign14Positive74ObjectMatrixGuard','nine-sharing-sign14-positive74-object-matrix-guard-check')]:
 key=f'/tmp/nine-sharing-sign14-positive74-object-positive-to-shift-open-retry02-check-20261110/lib/DiophantineConsistency/{mod}.olean';q=Path(key);st=json.loads((root/'research'/prior/'attempt01/state.json').read_text());assert q.is_symlink() and str(q.resolve())==b['overlay_links'][key] and sha(q)==st['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed internal shifted universal sentence implies guarded original nonzero open matrix; quantified closure separate'},indent=2))
