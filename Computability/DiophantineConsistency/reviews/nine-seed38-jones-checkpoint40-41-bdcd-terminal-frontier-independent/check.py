#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-checkpoint40-41-bdcd-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-checkpoint40-41-bdcd-check-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='79be3f29dbea9eadb6616763c863f50c61528f678804229d5b3e0e1c19c73981'
assert sha(A/'outer-terminal-author-record.json')=='3875f5f53e53c0d4800871997ea86ef40c71e2ad797f90b687068e1836339e13'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(11479,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1266
assert sha(P/'run.py')==s['runner_sha256']=='ca935170c5c323d99a73e8114d4c477542f473731e2e7614761fb0697618b09c'
assert s['base_state_sha256']=='561e4e5d025e6fae11eb8fc3d422e6e9ba6bab5735a98b92dd9b1e0d80474044'
objs=['513f20749d7aee8208b1a5379bf1617ea1619c73850175216158b5da66260a6b','28c1a6dc66fccad9142e640c5ff908d22ffbf7d8ca15cb283a812782820d334b','6d243292a8fca880882143a751e5daadb0cdfcc334a60ba880481c42f67325e2']
rows=[('Norm38MacroBdCdPaths','c6a94c2fd8de8ba867e19584545f81c603e18f0a85e838a8f1be5b19e7784a4e',200,{'Norm38MacroV1Value':'018456792e32aa046e8606769b7f8bbde3e53e8e1cf8c004f740ba7ebbb51601','Norm38MacroCheckpoint27to34':'92c83d8b5fbd508a804fabfc51aefb184225bda00a0a349d80374677258aab39','Norm38MacroCheckpoint34to41':'985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155'},['lookup39_41','lookup40_41','d41_C_value'],[]),('Norm38MacroBdValue','5e940e74c66e180d39493ea872279676628087f802cb4f792a0f7e7c56d18a4d',150,{'Norm38MacroBdCdPaths':objs[0],'Norm38MacroDependentBdCd':'c9f93896685c99df7b3dfdaf783d427f6a1150aeb48f70d56a9435597ce22940'},['d40_Bd_value'],[]),('Norm38MacroCdValue','b715d04d238e6b4ab467764120749e64b06fa8c93baedad9c9541e2c56519b36',100,{'Norm38MacroBdValue':objs[1]},['d41_Cd_value'],[])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointBdCd\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroCheckpointBdCd.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-checkpoint40-41-bdcd-prelaunch-frontier-independent';assert sha(R/'check.py')=='c4b62313d1d38d734520286289bdceddcf7ef977dff1c1519dca8770b3cd8e05' and sha(R/'result.json')=='18aa9a62cd7b5956ccdd789e94469fd68db7de300a1218e8890352384a01df26'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':11479,'stages':3,'guard_slots':450,'overlay_links':1266,'scope':'symbolic Bd and Cd and short-prefix C; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
