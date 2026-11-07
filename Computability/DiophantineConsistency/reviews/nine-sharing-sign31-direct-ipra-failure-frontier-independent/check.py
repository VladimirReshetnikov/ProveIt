#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-direct-ipra-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign31-direct-ipra-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='e5456b8359a20fd6a16265c5a790a4da13e92625f6885498b885f1c877503dc2' and sha(A/'outer-result.json')=='6216db601d2a3694bb7dc2e49243af134ba23db837a535063bfc816cbb85c6f3'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(75196,1) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1298 and s['runner_sha256']==sha(P/'run.py')=='acf8f183041b96927ded1af5112c0300e475f5b3452f3dcf2f0af2cf9090929c' and s['base_state_sha256']=='214196396eaa1ca0536edf65772ce03df4d03f637144683588cc768dc953f287'
r=s['rows'][0];n='Sign31AbstractExpressionDef';h='e3ef542e791067753258452618bd4f4767993713bd438e0dad9d96a8eab69181';assert r['module']==n and r['source_sha256']==h and len(r['direct_guard'])==150 and sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean')==h and 'object_sha256' not in r
for phase,exit in [('deps',0),('compile',-6)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
assert r['compile']['peak_session_rss_bytes']==2937880576
for mod,h in {'Sign32GenericRemoveInput':'0ab66daaacfbfa8f1d32649124c8eb12ca03e5b7881ca0134041e90152532e3b','Sign31CurrentSourceIff':'731041e2ed7302a0e2cb9fc0b8264be3195cd320ef6ccde407239ba57cd3d334'}.items():
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
err=(A/f'{n}-compile.txt').read_text();assert 'lean::memory_exception' in err and "at 'interpreter'" in err and 'depends on axioms' not in err
print(json.dumps({'status':'PASS_FAILURE_AUDIT','scope':'First symbolic definition-only module failed; internal operation is not identified. No first-stage object, later stages or whole-run postflight. Author-recorded outer outcome; no Lean replay.','author_session':75196,'lean_exit':-6,'sampled_peak_bytes':2937880576,'monitor_stop':None,'guard_slots':150,'overlay_links':1298},indent=2,sort_keys=True))
