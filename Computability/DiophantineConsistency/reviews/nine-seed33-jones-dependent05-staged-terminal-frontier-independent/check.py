#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent05-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-dependent05-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='70254e03d48c21f71f1ae4ae31a576d70491c9ff316ab65f9b0285ef35de38c9' and sha(A/'outer-terminal-author-record.json')=='8ca5342b266540b49aa152dcf49de84279046f8afb50276ce24562ae1d60da72';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(81983,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1098 and s['runner_sha256']==sha(P/'run.py')=='41308332d2ea978c66e1e6ceed793c20446e662a6111064392d72b01740b4157';names=['Sign33MacroDependentIcarry','Sign33MacroDependentE','Sign33MacroDependentF'];objects=['85a670d8908f67aa3808e77bde21522a6dd7e313a7b8b9057ac57d6337eb6280','cece31436221e187bb90f018ee6a62951416076114a42fc91e49832acc657038','e844c55fd2abd3abb4ca61dedbdc1d194a82a9a6e61cad757ee8b1879fa891c6'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d24_i_carry'],['d30_i_carry','d30_J_carry','d30_C_carry','prefix_E'],['d31_A_carry','prefix_F']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroDependentD','543e77ef6f0755c67375c1fe4e7be11d8e846a8c150177de7ecde1e3ad73a9a0') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroDependent05.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-dependent05-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='dead487cf533f4b15f65ae5c4686b8d274607a9d810635e5ddc8e9dd27e541bd'
up=D/'reviews/nine-seed33-jones-dependent04-staged-terminal-frontier-independent/check.py';assert sha(up)=='0591a9e298284e4892bf9e442c63a739024cb15501f22db8821c3ff176a95635';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':81983,'stages':3,'guard_slots':300,'overlay_links':1098,'scope':'local d31–d32 E/F prefix equations and carries only; no output equality'},indent=2,sort_keys=True))
