#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-terminal-cut-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-terminal-cut-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='ea7e7ce1a82e2e5a413e4888741cd574716db5ded19f0131191ac83332a975fb' and sha(A/'outer-terminal-author-record.json')=='8e47dbf235152444bb94e35d07c153c7b4a194da3543713a436d3239091d156c';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(15834,1)
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==2 and len(s['overlay_links'])==1272 and s['runner_sha256']==sha(P/'run.py')=='44d7d111b519fe9888f1708413b400f0febf371f96a2c4c39db066bffffc8b80' and s['base_state_sha256']=='83fa55209289b33a32df16eb39b04f9584b59d4aa5cfd19c04d6bda312d51ac3'
t,out=s['rows'];assert t['module']=='Norm38MacroTerminalT' and out['module']=='Norm38MacroTerminalOutput' and len(t['direct_guard'])==250 and len(out['direct_guard'])==100
obj='11e881a43e73f2646f2f7b137e8477ab202c35e9f1e19e1d12ecc6249b42aa49';assert t['object_sha256']==obj==sha(O/'lib/DiophantineConsistency/Norm38MacroTerminalT.olean') and 'object_sha256' not in out
for r,name,source,exit in [(t,'Norm38MacroTerminalT','bda39c06525a17959e951b2c689ed5f31571324a3b0aacfbdf2f3b489d4bddd3',0),(out,'Norm38MacroTerminalOutput','b7a3a71a4b27f29d3b018407dff71036e8188ced11d3996d214d73344ff81a36',1)]:
 assert r['source_sha256']==source==sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==(0 if phase=='deps' else exit) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
expected={'Norm38MacroDependentOutput':'39ae6b92258383e0505623a46c01a5ca71952561593a71090c0685508a7f8f58','Norm38MacroKcValue':'0b73715567a3ee4a5dd2a5117b35c489a3af154b9388e76a05d3e68e7b851d20','Norm38MacroPath18to41':'b245318d9c4049b569f3199955d2df27a31cdcfd49a1205ca2f8475801e32fa9','Norm38MacroPrefixInputsB':'43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170'}
for mod,h in expected.items():
 v=t['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and t['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
v=out['dependencies']['DiophantineConsistency.Norm38MacroTerminalT'];assert v['sha256']==obj and out['direct_guard'][v['path']]=={'sha256':obj,'realpath':v['realpath']}
log=(A/'Norm38MacroTerminalT-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
for name in ('lookup41_43','lookup41_44','d41_t_value','d44_T_cut'):assert re.search(r"'DiophantineConsistency\.Norm38MacroTerminalCut\."+name+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
err=(A/'Norm38MacroTerminalOutput-compile.txt').read_text();assert sha(A/'Norm38MacroTerminalOutput-compile.txt')=='2f5b1fca1813769a7ee1f237dbc96ed3a0ff916bdede76f5c31d4b807e658f1d' and 'error: Tactic `rewrite` failed' in err and 'd43.snoc' in err and 'sorryAx' in err
R=D/'reviews/nine-seed38-jones-terminal-cut-prelaunch-frontier-independent';assert sha(R/'check.py')=='7ce0c7c159c8fca231db72cd3790f05025ec0adbfb6270abc0c7f6941a4eb7c2' and sha(R/'result.json')=='5eb72c0249ae1eb3e7da05f4f3392e8b063a8800f2bd7d714369d347700f6feb'
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_AUDIT','author_recorded_outer_session':15834,'stage1':'pass, four standard axiom reports','stage2':'Lean exit1 at d44 snoc rewrite; error-contaminated sorryAx reports invalid','guard_slots':350,'overlay_links':1272,'scope':'T cut stage only; no successful output theorem or final whole-run postflight'},indent=2,sort_keys=True))
