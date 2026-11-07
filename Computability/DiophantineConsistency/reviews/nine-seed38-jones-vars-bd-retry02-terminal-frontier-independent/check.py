#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-bd-retry02';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-vars-bd-retry02-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='3723d26904e39f7606b3a3f844014033756e1b203ffe1f3aa452dde6f7947884'
assert sha(A/'outer-terminal-author-record.json')=='2afb17a0dfaffb7db533fe66704dae692833d70fb135eecaf4211428cb2af7c0'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(43726,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1274
assert sha(P/'run.py')==s['runner_sha256']=='3e1db39d2b54552fc0efacb5b8139a04cac665ecb03d9a7f1b96b992e1c36012'
assert s['base_state_sha256']=='b1709c2b60a6cd25b17ce55ead3e9aa3d5d570f15bf359e92c14c45012a046a7'
objs=['04918fb03433f8f26c2cf52f792235c47b4a7e9687dd967182f52a340d64e3f4']
rows=[('Norm38MacroVarsBd','099442f1db440cfb6a023d8ee11d5f8a253f5c02a51d1946d4af7731486d2bb4',100,{'Norm38MacroTerminalOutput':'d1362486f746e9dfeba1b94ae27f6bb770d8f15ed216fdcf2467f9a08a4bd474'},['d41_Bd_eq_dvsr'],[])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroVarsBd\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroVarsBd.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-vars-bd-retry02-prelaunch-frontier-independent';assert sha(R/'check.py')=='fc63c2b53bbdfe88c0565e19dc4ac9da480e6de588526a391d8964d8223b7c05' and sha(R/'result.json')=='106225f272a9cf28f3bde687d1cd89c30265dcaf6227da3e5ebf48a936dfd8bf'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':43726,'stages':1,'guard_slots':100,'overlay_links':1274,'scope':'symbolic Bd to vars.dvsr with opaque d11 rank; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
