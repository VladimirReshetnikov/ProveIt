#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-terminal-cut-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-terminal-cut-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='96c59bd40cf91ba6125d023fbf93c30fe64e77a6d8c26ba4b008fa2820a5355e' and H(A/'outer-terminal-author-record.json')=='f035381b7078edc952ef5dc4a758e2babc754c1087a07cf3e4d96dd27100e0f8';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(44278,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1165 and s['runner_sha256']==H(P/'run.py')=='4916d9b71d8e6cba98c52b78efb0853be99d93600b37be089e80074c3bc1b06f';names=['Sign33MacroTerminalT','Sign33MacroTerminalOutput'];objs=['bf56f31ab600781ebadd4aa72b1402643dc5153726a7b266cee3a9f0bbd94255','2f65b1af4a8a5ee5786093ca0b0ea9c47fe2a247926b461c9eddca0611823324'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroKcValue':'b5a5ca999049d1bb33c78707ca1df53cc9a1929837fa6922ffc8af31d518a2a9','Sign33MacroPath18to41':'d52d1483ef0134399692074405affe0dc2efecaabe4770e7e9bbd2800bb3ddcb','Sign33MacroPrefixInputsB':'1fa27bad80c2a5df777dd57235777d762bc4e7018ab9b830eb447467dc300ba8','Sign33MacroDependentOutput':'36c16fb1daf0dcde1169dfb9468f2657f4d6e48fcae7c29c4155b84c6a65ffe3',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[250,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 for th in ([['lookup41_43','lookup41_44','d41_t_value','d44_T_cut'],['d45_output_cut','recipe_output_cut']][i]):assert f"'DiophantineConsistency.Sign33MacroTerminalCut.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-terminal-cut-prelaunch-frontier-independent/check.py';assert H(pre)=='c920651f2f0860a1f76d68505215f6bade2e9b6b0a76ff7d92fd3445f2325da3';up=D/'reviews/nine-seed33-jones-checkpoint43-kc-terminal-frontier-independent/check.py';assert H(up)=='42d3b7bde1a5133c601dc2e40df0d18b1eb7c846e60a23c87a387f1f8bb57095';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':44278,'stages':2,'guards':350,'links':1165,'scope':'recipe T/output cuts in terms of earlier symbolic entries only; no full output semantics'},sort_keys=True,indent=2))
