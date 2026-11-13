#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-circuit-transition-probe-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='0a8113b45ed96450302cb94728b8c32869336b268a2f10b4523d96196075d07f' and sha(p/'source-manifest.json')=='5a9d7fd8437afe913378e5dbd19ed26e3db42453ebc7847ea85b8ef1d5bc640d'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74CircuitTransitionProbe';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74Circuit'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='2eefa0ccb7d27269f278296e61e101a879f605bccd32bea71582a663d692c3d5' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
previous=(root/'research/nine-sharing-sign14-positive74-circuit-eval-draft/Sign14Positive74CircuitEval.lean').read_text()
for a,b in (('def symArg','def circuitExpr'),('def numArg','def circuitEval')):
 assert ' '.join(previous.split(a,1)[1].split(b,1)[0].split()) in ' '.join(s.split())
for x in ('| n + 1 => symStep p (symState p n) (gateAt n)','| n + 1 => numStep p v (numState p v n) (gateAt n)','symState p 3 = [Sign14Positive74.g00 p, Sign14Positive74.g01 p, Sign14Positive74.g02 p]','numState p v 3 = [(Sign14Positive74.g00 p).evalRing v, (Sign14Positive74.g01 p).evalRing v, (Sign14Positive74.g02 p).evalRing v]'):assert x in s
for f in ('nine-sharing-sign14-positive74-circuit-eval-failure-independent','nine-sharing-sign14-positive74-circuit-eval-retry01-failure-independent','nine-sharing-sign14-positive74-circuit-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'first three symbolic and generic ring register-state transitions; no full circuit equality'},indent=2))
