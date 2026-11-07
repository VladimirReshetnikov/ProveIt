#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-direct-ipra-abstract-retry';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-direct-ipra-abstract-retry-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='fd2cce8f3af503cef01a09090be35789fd6180469bfc2eb63fad74ebc9271397' and sha(A/'outer-result.json')=='eae51a5963b7ffc5ca63bce8e164a18755f1c3395d151fc0fbbac49210719cbd'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(12321,1) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1286 and s['runner_sha256']==sha(P/'run.py')=='0c11306696ab068973592925f7e2d08e4431789264f365e222a78fb0769906ec' and s['base_state_sha256']=='0ea9a5c9e3b04cbf28979a4c61fc7359b768ea21e0da60bcf61b1792d64f560e'
r=s['rows'][0];n='Sign32AbstractExpression';h='dfd16e0ec3767a632fdb7b2c36f9077b01e3e11ea466323c0f9b5d44d1c54b67';assert r['module']==n and r['source_sha256']==h and len(r['direct_guard'])==150 and sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean')==h and 'object_sha256' not in r
for phase,exit in [('deps',0),('compile',-6)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
assert r['compile']['peak_session_rss_bytes']==2938646528
for mod,h in {'Sign32GenericRemoveInput':'0ab66daaacfbfa8f1d32649124c8eb12ca03e5b7881ca0134041e90152532e3b','Sign32CurrentSourceIff':'d5dce54ef8afdd6c9a55a9c4b00816bd091995a6a34b488f8f776053e627eda1'}.items():
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
err=(A/f'{n}-compile.txt').read_text();assert 'lean::memory_exception' in err and "at 'interpreter'" in err and 'depends on axioms' not in err
print(json.dumps({'status':'PASS_FAILURE_AUDIT','scope':'First abstract module failed; definition and theorem share this module, so failing declaration is not identified. No first-stage object, later stages or whole-run postflight. Author-recorded outer outcome; no Lean replay.','author_session':12321,'lean_exit':-6,'sampled_peak_bytes':2938646528,'monitor_stop':None,'guard_slots':150,'overlay_links':1286},indent=2,sort_keys=True))
