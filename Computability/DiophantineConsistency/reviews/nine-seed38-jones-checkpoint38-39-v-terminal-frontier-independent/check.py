#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-checkpoint38-39-v-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-checkpoint38-39-v-check-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='561e4e5d025e6fae11eb8fc3d422e6e9ba6bab5735a98b92dd9b1e0d80474044'
assert sha(A/'outer-terminal-author-record.json')=='fff4d2d64a379234e4c37f905ae3b1a286f12da03f6756bd22bf75f8acff520c'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(1442,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1264
assert sha(P/'run.py')==s['runner_sha256']=='99f864dd5ddb181240277fb1f97f639ab1d764c27071dc64e2ba3d85687fd5ef'
assert s['base_state_sha256']=='35a9cd0b5d1db0557e72c907996d2182f7a91526a3a8b90b716a291c698afbd4'
objs=['8e888e52d7ce8db1375a87f30d084cbd8f66269ab55d03d22b935c941375e034','018456792e32aa046e8606769b7f8bbde3e53e8e1cf8c004f740ba7ebbb51601']
rows=[('Norm38MacroV0Value','fa3a273626982de1411960918b2a4041684efd3e887fe7f6343e263d1c523154',150,{'Norm38MacroA1Path':'25cbbb07e0f5e0cf6190b544c5214d8f9ec6033f4357bd0565e74fd2729fef63','Norm38MacroDependentV':'93889388c58ac41b046d81d22bbdfd748ac726704bef2efe01ca6a132048d147'},['d38_V0_value'],[]),('Norm38MacroV1Value','970afa5a77f7c2e196c26da778a8645fb2946a019c68eae74c327625cb81bd1a',150,{'Norm38MacroV0Value':objs[0],'Norm38MacroDependentV':'93889388c58ac41b046d81d22bbdfd748ac726704bef2efe01ca6a132048d147'},['d39_V1_value'],[])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointV\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroCheckpointV.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-checkpoint38-39-v-prelaunch-frontier-independent';assert sha(R/'check.py')=='b3ffa1a3c754aba0d3769d7a0c55fedaa591f23331d3f5a670d8bb9e008aa804' and sha(R/'result.json')=='e01ddef777dc847648ceebb87fb502d054fd4a3e34cbb9fc26f2d4b6141ebb68'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':1442,'stages':2,'guard_slots':300,'overlay_links':1264,'scope':'symbolic V0 at d38 and V1 at d39; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
