#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-order-boundaries-early-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-order-boundaries-early-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==11574 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(p/'run.py')=='196aca5e06bea409be381fc449c79117003459a3124439d9e2ab43ba275b20bc';rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==len(s['rows'])==23 and [r['module'] for r in s['rows']]==[e['module'].split('.')[-1] for e in rows];pins={'Sign17DegreeCompose':'4af0d401fc347ac92ce4d038699b9b5b0db6dd020c879a5821040aef9dca7d82','Equiv':'fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f'};guards=warnings=0
for i,(r,e) in enumerate(zip(s['rows'],rows)):
 n=r['module'];assert r['source_sha256']==e['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for ph in ('deps','compile'):
  x=r[ph];log=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(out/log)==x['log_sha256']
  if i==22:assert sha(a/log)==x['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 for mod in e['imports']:
  dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
 obj=out/'lib/DiophantineConsistency'/(n+'.olean');log=(out/(n+'-compile.txt')).read_text();assert 'error:' not in log and 'sorryAx' not in log and r['object_sha256']==sha(obj);warnings+=log.count('warning:');pins[n]=r['object_sha256']
 if n.startswith('Sign17KWeightUnion') and n not in ('Sign17KWeightUnion96',):assert 'all_weights' in log and ' '.join(log.split()).count('[propext, Classical.choice, Quot.sound]')==2
assert warnings==15
log=(a/'Sign17KOrderBoundariesEarly-compile.txt').read_text();assert 'warning:' not in log and 'actual_boundary31_32' in log and 'actual_boundary95_96' in log and ' '.join(log.split()).count('[propext, Classical.choice, Quot.sound]')==2
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':11574,'outer_exit':0,'successful_children':23,'guard_entries':guards,'warnings':warnings,'scope':'actual-weight boundaries 31/32 and 95/96; global rank, K and file binding separate'},indent=2,sort_keys=True))
