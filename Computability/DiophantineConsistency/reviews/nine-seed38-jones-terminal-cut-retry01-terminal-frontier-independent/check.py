#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-terminal-cut-retry01';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-terminal-cut-retry01-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='b1709c2b60a6cd25b17ce55ead3e9aa3d5d570f15bf359e92c14c45012a046a7'
assert sha(A/'outer-terminal-author-record.json')=='c29f6d777c762ba761791f3667208c0f42c7830826da4604d83db350f3f8bf22'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(28036,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1272
assert sha(P/'run.py')==s['runner_sha256']=='e8afc64f48c674b519ad3b6925666e852369a766230dad59fb0df1aa81241d35'
assert s['base_state_sha256']=='83fa55209289b33a32df16eb39b04f9584b59d4aa5cfd19c04d6bda312d51ac3'
objs=['11e881a43e73f2646f2f7b137e8477ab202c35e9f1e19e1d12ecc6249b42aa49','d1362486f746e9dfeba1b94ae27f6bb770d8f15ed216fdcf2467f9a08a4bd474']
rows=[('Norm38MacroTerminalT','bda39c06525a17959e951b2c689ed5f31571324a3b0aacfbdf2f3b489d4bddd3',250,{'Norm38MacroDependentOutput':'39ae6b92258383e0505623a46c01a5ca71952561593a71090c0685508a7f8f58','Norm38MacroKcValue':'0b73715567a3ee4a5dd2a5117b35c489a3af154b9388e76a05d3e68e7b851d20','Norm38MacroPath18to41':'b245318d9c4049b569f3199955d2df27a31cdcfd49a1205ca2f8475801e32fa9','Norm38MacroPrefixInputsB':'43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170'},['lookup41_43','lookup41_44','d41_t_value','d44_T_cut'],[]),('Norm38MacroTerminalOutput','921487eb186ddf29bed53603ed925c72d91a9284fcb3be75698eccbf10ffef59',100,{'Norm38MacroTerminalT':objs[0]},['d45_output_cut','recipe_output_cut'],[])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroTerminalCut\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroTerminalCut.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-terminal-cut-retry01-prelaunch-frontier-independent';assert sha(R/'check.py')=='aed7584e1c07fbac43e5ab944cb9278d1262ea29c52dbfff9817f3fb59efc60c' and sha(R/'result.json')=='346b954696c17d37feb55d1b7fc42118c5b2a1e6de1102bd223fb53c47526c7a'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':28036,'stages':2,'guard_slots':350,'overlay_links':1272,'scope':'recipe output expressed using seven opaque cuts and input t; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
