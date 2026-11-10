#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-predecessor-retry01-check';old=root/'research/nine-sharing-sign14-positive74-object-predecessor-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='816fb3de9919e4dd7dd8cc95ada9de02f50754190d78bf13c1210d5878f3e60f' and sha(p/'source-manifest.json')=='5097193f8e27c4838aae8c71be84c17c701aa8b841cc7752c61c1938a3fd5f23'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectPredecessor';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
previous=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();before,rest=s.split('  have hv0 :',1);added,after=rest.split('  simpa [IPRAPredReconstruct.reconstruct',1);assert '![x, zero]' in added and '![x, succ (pred x)]' in added and added.count('apply funext')==2 and added.count('Fin.forall_fin_two')==2;recovered=before+'  simpa [IPRAPredReconstruct.reconstruct'+after.replace('Function.comp_def, hv0, hv1] using h','Function.comp_def] using h',1);assert recovered==previous
for f in ('nine-sharing-sign14-positive74-object-predecessor-failure-independent','nine-sharing-sign14-positive74-object-guard-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'framework-survey.py')],capture_output=True,text=True,check=True,timeout=180);v=json.loads(x.stdout);assert not x.stderr and v['status']=='PASS' and all(k in v['observed'] for k in ('IPRAPredReconstruct','IPRANativeAtomStability','IPRATheoryInstantiation','IntProver'))
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'open predecessor only; historical direct object pins not source-authenticated'},indent=2))
