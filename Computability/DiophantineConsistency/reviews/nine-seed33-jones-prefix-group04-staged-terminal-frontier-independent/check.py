#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group04-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-prefix-group04-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='6ea3f558560d46525b13296b76e6f084cd627eaedd9392beb1e928514363fb0b' and sha(A/'outer-terminal-author-record.json')=='318dd666c92443c1e5a997aaff06efc7ec485fa074aab1fd5f6218bb36bc28cc';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(14769,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1071 and s['runner_sha256']==sha(P/'run.py')=='a5e12cf380e5980f867aacc6d65db7c5a482d632e558408c9d4b26c946b51eaf';names=['Sign33MacroPrefixInputsA','Sign33MacroPrefixInputsB'];objects=['3cfc3529c97019bfa57f20d136eef22d4e822771b6cf2da051b5a6d9e61eacab','1fa27bad80c2a5df777dd57235777d762bc4e7018ab9b830eb447467dc300ba8'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['prefix_h','prefix_s','prefix_w'],['prefix_phi','prefix_i','prefix_j','prefix_t']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroPrefixGlarge','1887baa3203c288e248f8ee85eb0af794de72272dbde1c039a8774ebc4735e2f');v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroPrefixGroup04.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-prefix-group04-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='24b416ddae8e20ce04af49e86fd74fddae4d9039e9897b0873e0861805e7d376'
up=D/'reviews/nine-seed33-jones-prefix-group03-staged-terminal-frontier-independent/check.py';assert sha(up)=='ab4237754322f7aa5c7c769ce0068235e656272fc30a2f7e7910ab2559de8c22';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':14769,'stages':2,'guard_slots':200,'overlay_links':1071,'scope':'symbolic h/s/w/phi/i/j/t short prefixes only; no output equality'},indent=2,sort_keys=True))
