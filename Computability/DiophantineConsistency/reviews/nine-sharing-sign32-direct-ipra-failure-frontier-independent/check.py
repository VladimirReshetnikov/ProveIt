#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-direct-ipra-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-direct-ipra-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='f11b61fbb19eaf61c65ab9fe0341c449957ca66996181031894650a4bce0d042' and sha(A/'outer-result.json')=='79e47a1bd3caefec5f9f43ba9bc7e50b1722c10e390ec59ab463a7692c160da3';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(87971,1) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1285 and s['runner_sha256']==sha(P/'run.py')=='2c11e34c103b80453bfe822ba8af0a6fa86e8487915e69dfbc0de31aa227de34' and s['base_state_sha256']=='0ea9a5c9e3b04cbf28979a4c61fc7359b768ea21e0da60bcf61b1792d64f560e'
r=s['rows'][0];n='Sign32DirectExpression';h='6a24a8426c051d83a90323951e7768a372a26c38a8c7b3eed6d98d62cec6b683';assert r['module']==n and r['source_sha256']==h and len(r['direct_guard'])==150 and 'object_sha256' not in r and sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean')==h
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==(0 if phase=='deps' else -6) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
v=r['compile'];assert v['peak_session_rss_bytes']==2939711488 and v['rss_limit_bytes']==4294967296 and v['timeout_seconds']==120
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a' and 'lean::memory_exception' in log and "at 'interpreter'" in log and 'depends on axioms' not in log
for mod,h in [('Sign32CurrentSourceIff','d5dce54ef8afdd6c9a55a9c4b00816bd091995a6a34b488f8f776053e627eda1'),('ModelJonesSyntax','ca320ae03c5aece08482a0eb125d58c12d371ce524cce685428b0550a96c5171')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-sharing-sign32-direct-ipra-prelaunch-frontier-independent';assert sha(R/'check.py')=='053cee83bf65c52b9550bc532fd4eac67dff4c36c39e532e986f9094a7a1a818' and sha(R/'result.json')=='6bb7bad274496954d43d3264e816e70844c1c494ece5dbff87202b551de8a2e6'
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':87971,'deps_exit':0,'lean_exit':-6,'stop_reason':None,'sampled_peak_bytes':2939711488,'guard_slots':150,'overlay_links':1285,'scope':'interpreter memory exception, no proved stage1 object, stage2 and final postflight unrun'},indent=2,sort_keys=True))
