#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-succ-guard-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='6b084168ddca4b6bfb89d2547d7aafd13ec0b3751b0efb0e0b3b49c424e702b5' and sha(p/'source-manifest.json')=='a99cb39c7c1d012d7f91e2457337070f993460df9fd91c96654308c782764fb6'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectSuccGuard';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectShiftMatrix'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('∼eqAt (.func .succ (fun _ => a)) zero','NativeAxiom.basic BasicAxiomI.succNonzero','Rew.embSubsts (succVec v) ▹ Sign14Positive74ObjectGuard.guard','rw [guard_subst]','Entailment.Conj₂_intro','List.mem_map.mp hφ','succNonzeroOpen (v i)'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-shift-matrix-terminal-independent','nine-sharing-sign14-positive74-object-guard-bind-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
b=json.loads((root/'research/nine-sharing-sign14-positive74-object-shift-matrix-check/attempt01/state.json').read_text());key='/tmp/nine-sharing-sign14-positive74-object-shift-matrix-check-20261110/lib/DiophantineConsistency/Sign14Positive74ObjectGuardBind.olean';q=Path(key);st=json.loads((root/'research/nine-sharing-sign14-positive74-object-guard-bind-check/attempt01/state.json').read_text());assert q.is_symlink() and str(q.resolve())==b['overlay_links'][key] and sha(q)==st['rows'][0]['object_sha256']
assert 'List.finRange 14' in (root/'research/nine-sharing-sign14-positive74-object-guard-check/src/DiophantineConsistency/Sign14Positive74ObjectGuard.lean').read_text()
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed native successor nonzero and exact 14-coordinate instantiated guard; quantified closure separate'},indent=2))
