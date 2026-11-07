#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-kc-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-vars-kc-check-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='26bc4134282e64e3915acb773730c6c87f2c35ca190074d0e4401fa524165d1d'
assert sha(A/'outer-terminal-author-record.json')=='e5c00cbf0824b68ef2e754cfc339414613c7ec5ad60234f33aa50846af6df37e'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(71529,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1280
assert sha(P/'run.py')==s['runner_sha256']=='593caa4dadefdad8569e024d5e8cc63b0a56c60e67626efd6e4a32fa684ad13f'
assert s['base_state_sha256']=='22a3472ca55b1681b4fe4f51ca43e4ca97f3b054d52d6da3ffa75b4482575514'
objs=['38c669f913f9a38059756c3a40ca979814ee1cc3ceb645b20e15a418d490e20d','cb7a316ae929ac862636d460e7b8da8be066cfd23555be8ee3958f0b0ce4e041']
rows=[('Norm38MacroVarsDm','eee78f45150d3b4f47ff6723fe76daf2226db330e62512941cb300a0d7fc339c',100,{'Norm38MacroVarsWt1':'c1317d8835be2a9775fda42b676fb4f117206ef456bcd57af9fa53df1dd32347'},['d42_Dm_eq_marg'],[]),('Norm38MacroVarsKc','9b4bddfa3add30f4502b242af00f4c56f23ad6e9639e80a08009f891b513a491',100,{'Norm38MacroVarsDm':objs[0]},['d43_Kc_eq'],[])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroVarsKc\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroVarsKc.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-vars-kc-prelaunch-frontier-independent';assert sha(R/'check.py')=='73d7e266f4221925566ebe59f2eecee21112087a8d9ae4e11574a5c3cae78cc9' and sha(R/'result.json')=='d32f3f8bf6f8e4e8c97fd181d8cb46484c597c54a42d8fd30b9a698c48b1abec'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':71529,'stages':2,'guard_slots':200,'overlay_links':1280,'scope':'symbolic Dm/marg and Kc/dvsr cuts; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
