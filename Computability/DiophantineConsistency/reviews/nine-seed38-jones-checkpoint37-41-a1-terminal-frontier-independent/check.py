#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-checkpoint37-41-a1-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-checkpoint37-41-a1-check-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='35a9cd0b5d1db0557e72c907996d2182f7a91526a3a8b90b716a291c698afbd4'
assert sha(A/'outer-terminal-author-record.json')=='b258d7fba35f84fdd2c0ef9254ae453ac065a9de2bb72a59829013c870d1c7f9'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(38602,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1262
assert sha(P/'run.py')==s['runner_sha256']=='ac8130ae9329e12f6f896fce1032e5e42d0ed7fdbb4ed27a836a8712ca4d25cb'
assert s['base_state_sha256']=='3223b4ced8c30d3f1de22fdd621720d0081fea7ee6ff05ee45921c8bd0ca9404'
objs=['0888f585cafebdc9e8c5f51dc0d28a3369893ca91ecdae28bba8e1713738dd8e','25cbbb07e0f5e0cf6190b544c5214d8f9ec6033f4357bd0565e74fd2729fef63']
rows=[('Norm38MacroA1Value','124f298cb19240027583814ef65f4b721f6fc5378d5b36fa239836fd6cbae9c5',150,{'Norm38MacroA0Path':'d8915cf6fe8fc9245466662f0d3c6389a0d4141d36af507fa8797d580ff5c043','Norm38MacroDependentA1':'ceafb76103e30efb1f9c8a9cb4c57ec2c9d294c5a6c4c6f5b85fb6f1bcc58513'},['d37_A1_value'],[]),('Norm38MacroA1Path','7660db034acc402ee4e6770ef41ca132c61544eb346010f4ee70cec91fb0b9a0',100,{'Norm38MacroA1Value':objs[0]},['lookup37_41','d41_A1_value'],['path37_41'])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointA1\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroCheckpointA1.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-checkpoint37-41-a1-prelaunch-frontier-independent';assert sha(R/'check.py')=='d0ef2b8c86300bda2fb8d45bbf0b5b6028f13b0f1dbdb76c8100d18875307744' and sha(R/'result.json')=='81fb7b68fee9417bd67ced83514806ba8fa6a45c9eddb98620a95ad18cd7b0dc'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':38602,'stages':2,'guard_slots':250,'overlay_links':1262,'scope':'symbolic A1 at d37 and d41; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
