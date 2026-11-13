#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-named-equality-retry03';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-named-equality-retry03-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='d21b1085b490c2066e3a660af22867ae48079f4ab9dfdccda596c63eea93b162' and sha(A/'outer-terminal-author-record.json')=='57f5be6347ba11d8fe249a598e4e97751cfb9f376ea61076d2f9b0158175ef43';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(35036,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1283 and s['runner_sha256']==sha(P/'run.py')=='78a328c5dc8842f909b96153d1194292df765ad3706203b7070c4a8c5e38a985';names=['Norm38MacroNamedVars','Norm38MacroNamedEquality'];objects=['2b5e7d2dc617b6be53a0447a28ec61af7cfc969b541b4c00409b294fff33500b','7133b01ee91487f7d2109b23f5b06fae7b56dda275a412c1d150ca1f2640a577'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[150,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 expected={'Norm38MacroVarsOutput':'068b76a14eb12512b8a83b72feb31be24e2a8a21977bc76998c3b52ff4b1d4b5','Norm38NamedFormula':'f628947fecd14dec5840ed18aa4b362c8e1173e6cf4fbdb60722c428e23b2725'} if i==0 else {names[0]:objects[0]}
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();th=['vars_eq_named','recipe_eq_expression_eval'][i];assert f"'DiophantineConsistency.Norm38MacroNamedEquality.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split()) and 'sorryAx' not in log
 if i==0:assert log.count('warning:')==1 and 'linter.unnecessarySeqFocus' in log
 else:assert 'warning:' not in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed38-jones-named-equality-retry03-prelaunch-frontier-independent/check.py';assert sha(review)=='639b49f7462afa07f639f5149d0851b41416d882bbc0aa99d02e7aab0cd0a319';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':35036,'stages':2,'guard_slots':250,'overlay_links':1283,'warning':'one unnecessarySeqFocus linter warning','scope':'Lean recipe output equals Lean expression evaluation for every commutative ring and Fin9 valuation; no JSON or prose binding'},indent=2,sort_keys=True))
