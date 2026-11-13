#!/usr/bin/env python3
"""Audit sign17 lower-bound partial failure without Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-mc-compose-core-retry-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-mc-compose-core-retry-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==3474 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(p/'run.py')=='b7a17c838e41e4859d32d76d20e214edcd7e074366db0b0a63baaeacc5cc3edf';rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(s['rows'])==19 and [r['module'] for r in s['rows']]==[e['module'].split('.')[-1] for e in rows[:19]];pins={'GeomSum':'f7b10e5ff78ec4af74841d77f6d5c4776c3c31c67df7d3dda1d91b79a1ad4ff0','Sign17DegreeCompose':'4af0d401fc347ac92ce4d038699b9b5b0db6dd020c879a5821040aef9dca7d82','Equiv':'fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f'};guards=0
for i,(r,e) in enumerate(zip(s['rows'],rows)):
 n=r['module'];src=p/'src/DiophantineConsistency'/(n+'.lean');assert r['source_sha256']==e['source_sha256']==sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for phase in ('deps','compile'):
  x=r[phase];log=n+'-'+phase+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(out/log)==x['log_sha256']
  if i==18:assert sha(a/(phase+'.txt'))==x['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 for mod in e['imports']:
  dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
 obj=out/'lib/DiophantineConsistency'/(n+'.olean');log=(out/(n+'-compile.txt')).read_text()
 assert 'error:' not in log and 'sorryAx' not in log and r['object_sha256']==sha(obj);pins[n]=r['object_sha256']
 if i==13:assert 'expression_polynomial_degree_ge' in log and '[propext, Classical.choice, Quot.sound]' in ' '.join(log.split()) and r['object_sha256']=='eb611521a7312ed3766154c9a36147091969b8a0edbdf977af8c6205dab8d2ce'
 if i==14:assert all(t in log for t in ('current_port_positive','current_port_nonzero','abstract_exact','current_exact')) and ' '.join(log.split()).count('[propext, Classical.choice, Quot.sound]')==4 and r['object_sha256']=='93d2cabd70b1f6e0985a89d3f72ebe74e24a7a9f26c6c197f6af6f5c18d4baa0' and 'warning:' not in log
 if i==15:assert r['object_sha256']=='8b757a0fc805556cab9c7b4fec50ffb50f1ad40dfdbcc264175e07c5699920ea' and log.count('warning:')==1
 if i==16:assert r['object_sha256']=='b0c8e2eea89e13177ba49066495836608f0ca2356d615e378d5e5eaf20e0d447'
 if i==17:assert r['object_sha256']=='6697165d359a9f135574717ca1932a48c18b7a2e972a37da1881238c694ad494'
 if i==18:assert all(t in log for t in ('radix_alignment','aligned_repeat','aligned_append','flatten_tail')) and r['object_sha256']=='d7f0c536ead4c539deedf786ef397d62198da65d9ce3ee287ebedc721b7d3663' and 'warning:' not in log and log.count('[propext]')==4
assert pins['Sign17AxisDiagonalDegree']=='57caa32eb4255b3a4d59a2b6365644ce5eedec62aa70c62a8f1c5cbec055ad19';assert pins['Sign17AxisDiagonalBinding']=='1c1d934b60ad17fd87180f4df847b219e620da0c25026ffd2e70e0241238e0af'
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':3474,'outer_exit':0,'successful_children':19,'guard_entries':guards,'scope':'generic block composition only; no whole-port or file binding'},indent=2,sort_keys=True))
