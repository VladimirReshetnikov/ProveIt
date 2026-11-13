#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-circuit-eval-retry01-check';old=root/'research/nine-sharing-sign14-positive74-circuit-eval-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='67783049d49ca964e5c706d1d3b033520eef51fa08c25ae0afe5ce618b8926cf' and sha(p/'source-manifest.json')=='d90ba72a3487cfcd9d5cff384c1f3ae17fa6a303bf48136c236c1de34263ce77'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74CircuitEval';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();prior=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert prior.replace('theorem circuitExpr_eq','set_option maxHeartbeats 1000000 in\ntheorem circuitExpr_eq').replace('theorem circuitEval_eq','set_option maxHeartbeats 1000000 in\ntheorem circuitEval_eq')==s and sha(q)==sha(repo/e['source'])==e['source_sha256'] and e['imports']==json.loads((old/'source-manifest.json').read_text())['rows'][0]['imports']
for f in ('nine-sharing-sign14-positive74-circuit-eval-failure-independent','nine-sharing-sign14-positive74-circuit-eval-source-independent','nine-sharing-sign14-positive74-circuit-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'heartbeat-only retry at 1m per equality; same ring/symbolic evaluator statements and 120s/4GiB outer guards'},indent=2))
