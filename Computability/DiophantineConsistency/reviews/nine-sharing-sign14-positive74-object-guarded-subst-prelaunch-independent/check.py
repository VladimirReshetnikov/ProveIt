#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-guarded-subst-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='e7cf7bc2caadd5e4c58683f80bec8c070af0486ee087b07a794181504a54b61d' and sha(p/'source-manifest.json')=='50af81abc2824cd59dbf4962dae0cbf5e430d62e4bbc93e8dbe38722a1250b59'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectGuardedSubst';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectMultiSubst'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('fun i => succ (pred (v i))','Semisentenceᵢ language 14','(Rew.embSubsts v ▹ Sign14Positive74ObjectGuard.guard) 🡒','(Rew.embSubsts (predSuccVec v) ▹ φ)','guardedAllSubstitution φ v (predSuccVec v)','(nonzeroGuardOpen v) (fun i => reconstructionAt v i)','simpa only [guard_subst] using h'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-multisubst-retry03-terminal-independent','nine-sharing-sign14-positive74-object-coordinate-elim-retry02-terminal-independent','nine-sharing-sign14-positive74-object-guard-bind-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
b=json.loads((root/'research/nine-sharing-sign14-positive74-object-multisubst-retry03-check/attempt01/state.json').read_text());base='/tmp/nine-sharing-sign14-positive74-object-multisubst-retry03-check-20261110/lib/DiophantineConsistency/'
for mod,folder in [('Sign14Positive74ObjectCoordinateElim','nine-sharing-sign14-positive74-object-coordinate-elim-retry02-check'),('Sign14Positive74ObjectGuardBind','nine-sharing-sign14-positive74-object-guard-bind-check')]:
 old=json.loads((root/'research'/folder/'attempt01/state.json').read_text());k=base+mod+'.olean';v=b['overlay_links'][k];assert Path(k).resolve()==Path(v).resolve() and sha(Path(v))==old['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed 14-coordinate guarded open substitution to successor-of-predecessor vector'},indent=2))
