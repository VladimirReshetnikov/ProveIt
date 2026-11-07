#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-checkpoint43-kc-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-checkpoint43-kc-check-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='83fa55209289b33a32df16eb39b04f9584b59d4aa5cfd19c04d6bda312d51ac3'
assert sha(A/'outer-terminal-author-record.json')=='4420c537233e38592dfcbf5fb2dac49b5ef75afd12f2815e90e4f186f9266fb3'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(27919,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1271
assert sha(P/'run.py')==s['runner_sha256']=='ee0bcfd5cb5a522cceb6ac5bff27be47b215b87a617b63662f7979998b55cd73'
assert s['base_state_sha256']=='66b0e34af2cae85fb44fce028f6245fbdbc2f9ea8eb8556b12d173d1c9f8265d'
objs=['0b73715567a3ee4a5dd2a5117b35c489a3af154b9388e76a05d3e68e7b851d20']
rows=[('Norm38MacroKcValue','c754b51cffbadef259c6c2a6196a704d84909cb8b80850261abf14ae270d005b',100,{'Norm38MacroDmValue':'d7e21e6b765a1a796c0f87165394188f19bc25df619a32fd7d9d8780948c803a'},['d42_Bd_value','d43_Kc_value'],[])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointKc\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroCheckpointKc.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-checkpoint43-kc-prelaunch-frontier-independent';assert sha(R/'check.py')=='1e6184b0ced6f54ecee6fd5ee0403b8b9418cb770dfd78318b766534117f64b3' and sha(R/'result.json')=='aed7ef45dfec24ddf6d00918c0e1b2e739599fc55dcfa256509af060f72ef1ed'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':27919,'stages':1,'guard_slots':100,'overlay_links':1271,'scope':'symbolic Bd at d42 and Kc at d43; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
