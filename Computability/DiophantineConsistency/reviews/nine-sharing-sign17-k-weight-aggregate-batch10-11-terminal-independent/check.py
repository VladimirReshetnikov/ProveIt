#!/usr/bin/env python3
"""Audit sign17 lower-bound partial failure without Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-weight-aggregate-batch10-11-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-weight-aggregate-batch10-11-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==79602 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(p/'run.py')=='caa992580502cdfe4b6a761788f9cb78028cc95a96bdee7de9a4fcb2205dfdd0';rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(s['rows'])==17 and [r['module'] for r in s['rows']]==[e['module'].split('.')[-1] for e in rows[:17]];pins={'Sign17DegreeCompose':'4af0d401fc347ac92ce4d038699b9b5b0db6dd020c879a5821040aef9dca7d82','Equiv':'fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f'};guards=0
for i,(r,e) in enumerate(zip(s['rows'],rows)):
 n=r['module'];src=p/'src/DiophantineConsistency'/(n+'.lean');assert r['source_sha256']==e['source_sha256']==sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for phase in ('deps','compile'):
  x=r[phase];log=n+'-'+phase+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(out/log)==x['log_sha256']
  if i>=15:assert sha(a/(n+'-'+phase+'.txt'))==x['log_sha256']
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
 if i==15:assert 'all_weights' in log and ' '.join(log.split()).count('[propext, Classical.choice, Quot.sound]')==1 and 'warning:' not in log and r['object_sha256']=='77f522dff68df1765a3195798684e3a65ecb93b17b9283ea114bbbf99f8104f0'
 if i==16:assert 'all_weights' in log and ' '.join(log.split()).count('[propext, Classical.choice, Quot.sound]')==1 and 'warning:' not in log and r['object_sha256']=='dc581291b230cd3e996aa36997a77dc5e65afe339a3f099a03142670ce863f12'
assert pins['Sign17AxisDiagonalDegree']=='57caa32eb4255b3a4d59a2b6365644ce5eedec62aa70c62a8f1c5cbec055ad19';assert pins['Sign17AxisDiagonalBinding']=='e74acbaecc8e0228d13cab7c3a705edcb246c6bb4b11f09655b341f92b46af74'
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':79602,'outer_exit':0,'successful_children':17,'guard_entries':guards,'scope':'two universal Fin64 actual Lean tile-weight identities, no full ranking/K/file theorem'},indent=2,sort_keys=True))
