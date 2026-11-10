#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-circuit-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='e9b36baecc392f1e2677fd80e9286fe74ea896a57a127112c46cac4388c57e93' and sha(p/'source-manifest.json')=='817e86f93cb5f536d3a90998dea52f9b458efc1291ae7d03aaedef57098c2af8'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74Circuit';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectEndpoint'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='c92c1a2ecd728fcc16364b30d2d32a055b1063bbcb08a49fc5a994535789e3ba' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('gates.length = 74','theorem topological','theorem operationCounts','theorem parentCertificate','inductive Live','theorem everyGateLive'):assert z in s
for f in ('nine-sharing-sign14-positive74-circuit-source-independent','nine-sharing-sign14-positive74-object-endpoint-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed count/topology/liveness for 74-gate register DAG; circuit semantics and file binding separate'},indent=2))
