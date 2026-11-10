#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-circuit-transitions-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='c89d5c4900c6b4628eb1f4fe47eaebce2d20c510c9cceab3c7011587fbe64158' and sha(p/'source-manifest.json')=='17f4169be07e6d3a36b296e4ed35f90f78b6588c7b49236a81f139b46a2395f8'
audit=json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-circuit-transitions-source-independent/check.py')],capture_output=True,text=True,check=True,timeout=180).stdout);assert audit['status']=='PASS_SOURCE_AUDIT' and audit['modules']==9 and audit['symbolic_and_ring_state_theorems']==142
es=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(es)==9
for i,e in enumerate(es):
 n=f'Sign14Positive74CircuitTransitions{i:02}';src=p/'src/DiophantineConsistency'/(n+'.lean');prior='Sign14Positive74CircuitTransitionProbe' if i==0 else f'Sign14Positive74CircuitTransitions{i-1:02}';assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.'+prior] and re.findall(r'^import (\S+)$',src.read_text(),re.M)==e['imports'] and sha(src)==sha(repo/e['source'])==e['source_sha256']==audit['source_sha256'][src.name]
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-circuit-transition-probe-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r and 'local producer ' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and json.loads(x.stdout)['stage_count']==9
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'nine staged 71 symbolic/ring register-state transitions; full output equality and external file binding separate'},indent=2))
