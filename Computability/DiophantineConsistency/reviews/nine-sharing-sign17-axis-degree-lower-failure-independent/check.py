#!/usr/bin/env python3
"""Audit sign17 lower-bound partial failure without Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-axis-degree-lower-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-axis-degree-lower-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==77502 and o['outer_exit_code']==1 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign17AxisDiagonalBinding')" and s['runner_sha256']==sha(p/'run.py')=='242b771c009a964bf82a450221541d57f052f5dfa838ab544bc6dc4a46b55368';rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(s['rows'])==13 and [r['module'] for r in s['rows']]==[e['module'].split('.')[-1] for e in rows[:13]];pins={'Sign17DegreeCompose':'4af0d401fc347ac92ce4d038699b9b5b0db6dd020c879a5821040aef9dca7d82','Equiv':'fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f'};guards=0
for i,(r,e) in enumerate(zip(s['rows'],rows)):
 n=r['module'];src=p/'src/DiophantineConsistency'/(n+'.lean');assert r['source_sha256']==e['source_sha256']==sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for phase in ('deps','compile'):
  x=r[phase];log=n+'-'+phase+'.txt';assert x['exit']==(1 if i==12 and phase=='compile' else 0) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(out/log)==x['log_sha256']
  if i==12:assert sha(a/(phase+'.txt'))==x['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 for mod in e['imports']:
  dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
 obj=out/'lib/DiophantineConsistency'/(n+'.olean');log=(out/(n+'-compile.txt')).read_text()
 if i<12:assert 'error:' not in log and 'sorryAx' not in log and r['object_sha256']==sha(obj);pins[n]=r['object_sha256']
 else:assert log.count('error:')==1 and 'case var' in log and 'sorryAx' in log and not obj.exists() and 'object_sha256' not in r
assert pins['Sign17AxisDiagonalDegree']=='57caa32eb4255b3a4d59a2b6365644ce5eedec62aa70c62a8f1c5cbec055ad19';assert not (out/'lib/DiophantineConsistency/Sign17AxisDegreeLower.olean').exists()
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_AUDIT','outer_session':77502,'outer_exit':1,'successful_children':12,'failed_child':'Sign17AxisDiagonalBinding','guard_entries':guards,'scope':'diagonal bound compiled; binding failed at variable case with sorryAx; no binding/lower object or postflight'},indent=2,sort_keys=True))
