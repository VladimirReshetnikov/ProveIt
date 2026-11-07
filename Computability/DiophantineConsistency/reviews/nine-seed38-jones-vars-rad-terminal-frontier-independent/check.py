#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-rad-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-vars-rad-check-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='8643b1814c0c4ef4513f5b8e39c9ca74eb45c1c0f5da7febeaacb1199d17824e'
assert sha(A/'outer-terminal-author-record.json')=='eb9abc8625e094cd9a3fa1d105841daef0290d0364e81b11ff3216f373a179f7'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(51435,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1276
assert sha(P/'run.py')==s['runner_sha256']=='1e2a86647e018c8b21734f8603296cdb9c771f7bf253895f75708382dad2e2a0'
assert s['base_state_sha256']=='71450c1f5044e62f3b2a10eab7d443b3cf4b6c07f5133d29060b9fe43be71de4'
objs=['3551c3dc5182e269c9ec729c5dce38a151f73985876997755e983c1d477d90a1','76684ed48a14cc0329ccd3000599e76b1dfcc420aae03bfb8a6ff3b711850fc2']
rows=[('Norm38MacroVarsRad0','15b8415073861f7ff7f32a25804fcc3c8c22163aa710bccc633d04dfaf7036c7',100,{'Norm38MacroVarsCd':'1dfc9cbdefc4f7ec437dd2acd3b09bd1668897e263bdfa96c8ffe5182e349138'},['d41_A0_eq_rad0'],[]),('Norm38MacroVarsRad1','402cdf6d0bde2f0f0cbb14e28942a92f2ed50aa48b03c7465a1d54de8d221c5a',100,{'Norm38MacroVarsRad0':objs[0]},['d41_A1_eq_rad1'],[])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroVarsRad\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroVarsRad.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-vars-rad-prelaunch-frontier-independent';assert sha(R/'check.py')=='222802c84d66fddb774411cd88e90c2a65152381e8035d0992614bd0f009e588' and sha(R/'result.json')=='c406104c589e3464dc1e661e43c7d194bda83742554c4279ccd391bd8eec7d36'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':51435,'stages':2,'guard_slots':200,'overlay_links':1276,'scope':'symbolic A0/A1 to vars.rad0/rad1; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
