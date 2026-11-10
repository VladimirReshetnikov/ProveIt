#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-sentence-iff-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='99f0a24fbbe3fc9e7414fefad854a0b99a42b4bac437a6696492eaaf608e35f5' and sha(p/'source-manifest.json')=='d163744c81705a29213193573f2c0e5edb8e38de064ca509c22ef6098d69c9f8'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectSentenceIff';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectCloseImp'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(positiveNoZero e 🡒 nativeNoZero (positiveShift e))','(nativeNoZero (positiveShift e) 🡒 positiveNoZero e)','(positiveNoZero e 🡘 nativeNoZero (positiveShift e))','closeImp14 (positiveNoZero e) (∼equalityMatrix (positiveShift e))','positiveToShiftOpen e freeVec','closeImp14 (nativeNoZero (positiveShift e)) (guard 🡒 ∼equalityMatrix e)','shiftToPositiveOpen e freeVec','Entailment.K_intro (guardedToShift e) (shiftToGuarded e)'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-close-imp-terminal-independent','nine-sharing-sign14-positive74-object-positive-to-shift-open-retry02-terminal-independent','nine-sharing-sign14-positive74-object-shift-to-positive-open-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
b=json.loads((root/'research/nine-sharing-sign14-positive74-object-close-imp-check/attempt01/state.json').read_text())
for mod,prior in [('Sign14Positive74ObjectPositiveToShiftOpen','nine-sharing-sign14-positive74-object-positive-to-shift-open-retry02-check'),('Sign14Positive74ObjectShiftToPositiveOpen','nine-sharing-sign14-positive74-object-shift-to-positive-open-check')]:
 key=f'/tmp/nine-sharing-sign14-positive74-object-close-imp-check-20261110/lib/DiophantineConsistency/{mod}.olean';q=Path(key);st=json.loads((root/'research'/prior/'attempt01/state.json').read_text());assert q.is_symlink() and str(q.resolve())==b['overlay_links'][key] and sha(q)==st['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed native object-language biconditional between guarded and shifted sentences for arbitrary Fin14 expression; concrete endpoint/PDF separate'},indent=2))
