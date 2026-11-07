#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-ordered-ring-check';A=P/'attempt01';O=Path('/tmp/sign26-ordered-ring-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='0f0699ba5707d14b403e48e7f9e7c8fa4596bd94bd4647d38be4f067bfb70b25' and H(A/'outer-result.json')=='07c0f107ddad805a3e12bd887084183d2dc580bb303f4102acc224bf07d0eb19';s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(25058,1) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='9924fd13a40b8db3b127b486692cd7ac0e8ad421ad6fcd902c73dbd36d7f1e00' and s['source_sha256']==H(P/'src/Sign26OrderedRing.lean')==H(O/'src/Sign26OrderedRing.lean')=='5f00ccfb2c2f23664ca46cebff1a6e0ca861541bb1f6c7fc524eda32cdc0d390' and len(s['direct_guard'])==60
r=s['rows'][0];assert r['module']=='Sign26OrderedRing'
for phase,ex in [('deps',0),('compile',1)]:
 v=r[phase];assert v['exit']==ex and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'Sign26OrderedRing-{phase}.txt')==H(O/f'Sign26OrderedRing-{phase}.txt')==v['log_sha256']==o['logs'][f'Sign26OrderedRing-{phase}.txt']
log=(A/'Sign26OrderedRing-compile.txt').read_text();assert log.count('error: unknown tactic')==2 and log.count('error: unsolved goals')==2 and log.count('sorryAx')==2 and 'a * (a + 1) + t - a * n = a * (a + 1 - n) + t' in log;assert 'object_sha256' not in r and not (O/'lib/Sign26OrderedRing.olean').exists()
for path,v in s['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,v in r['dependencies'].items():assert s['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
pre=D/'reviews/nine-sharing-sign26-ordered-ring-prelaunch-frontier-independent/check.py';assert H(pre)=='907bada737fb224da74398e524b2b3915ff8658a5c14fa5c2622bb600af695dd'
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':25058,'deps_exit':0,'compile_exit':1,'guards':60,'scope':'two unknown ring tactics; both axiom reports error-contaminated; no object or final postflight'},sort_keys=True,indent=2))
