#!/usr/bin/env python3
"""Audit sign17 lower-bound partial failure without Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-order-batch02-03-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-order-batch02-03-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==12126 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(p/'run.py')=='6b6b3822b91fea94f6483256d61b69e9b5fb011202fc77f743538e931d258cda';rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(s['rows'])==20 and [r['module'] for r in s['rows']]==[e['module'].split('.')[-1] for e in rows[:20]];pins={'Sign17DegreeCompose':'4af0d401fc347ac92ce4d038699b9b5b0db6dd020c879a5821040aef9dca7d82','Equiv':'fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f'};guards=0
for i,(r,e) in enumerate(zip(s['rows'],rows)):
 n=r['module'];src=p/'src/DiophantineConsistency'/(n+'.lean');assert r['source_sha256']==e['source_sha256']==sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for phase in ('deps','compile'):
  x=r[phase];log=n+'-'+phase+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(out/log)==x['log_sha256']
  if i>=17:assert sha(a/(n+'-'+phase+'.txt'))==x['log_sha256']
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
 if i in (17,18):assert all(x in log for x in ('indices_ne_zero','adjacent','actual_adjacent')) and ' '.join(log.split()).count('[propext, Classical.choice, Quot.sound]')==3 and 'warning:' not in log and r['object_sha256']==(['da7c41db6fc3eeca7e7b0e54497125d2298c4402cd2f716df7ae0c73c14efa85','38c6a7c2cb412cfb5fa21684454346f311d6ae3abd74b42b02e2fbfc5f5501cb'][i-17])
 if i==19:assert all(x in log for x in ('boundary','actual_boundary')) and ' '.join(log.split()).count('[propext, Classical.choice, Quot.sound]')==1 and '[propext]' in log and 'warning:' not in log and r['object_sha256']=='912db7b23c7cfe5758bd24f32a7a3f9856fdf0740ba661acd4294ff78ad1d76c'
assert pins['Sign17AxisDiagonalDegree']=='57caa32eb4255b3a4d59a2b6365644ce5eedec62aa70c62a8f1c5cbec055ad19';assert pins['Sign17AxisDiagonalBinding']=='934dc6579c71c3fdae72448f6ec3c63cb56042f5b305a4217737f36ca952568d'
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':12126,'outer_exit':0,'successful_children':20,'guard_entries':guards,'scope':'blocks 96–223 and one boundary actual-weight order certificates, no full ranking/K/file theorem'},indent=2,sort_keys=True))
