#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-circuit-retry01-check';old=root/'research/nine-sharing-sign14-positive74-circuit-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='0883c9a760a934af933394bc9a2d838880381a71b205bb7540ec0208c9b20149' and sha(p/'source-manifest.json')=='3543d6f623293712dbbeae89232ab694aff470f5f9f238e30d76aa0f1f9c3864'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74Circuit';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();prior=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();a="        have hp := parentCertificate ⟨j, hj'⟩\n";b=a+'        change j < parentAt j ∧ parentAt j < 74 ∧\n          ((gateAt (parentAt j)).left = .reg j ∨\n           (gateAt (parentAt j)).right = .reg j) at hp\n';assert prior.count(a)==1 and prior.replace(a,b)==s and sha(q)==sha(repo/e['source'])==e['source_sha256'] and e['imports']==json.loads((old/'source-manifest.json').read_text())['rows'][0]['imports']
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-circuit-failure-independent/check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-circuit-source-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proof-only Fin-index normalization; same proposed circuit count/topology/liveness; evaluator semantics separate'},indent=2))
