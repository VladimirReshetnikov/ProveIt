#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group03-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-prefix-group03-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='f1769a73743919a3ff52d3637a514592fdbd5d5222669bc17c404ecee33a29d0' and sha(A/'outer-terminal-author-record.json')=='bded56ced816754aa7cb64deef76dc184d9efe7766b7a01f030692d4a3c1d47f';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(27321,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1067 and s['runner_sha256']==sha(P/'run.py')=='63bb7c33e55687f7c054d4dee524bdd7d8221001ce1873fb99af0439ee2ed0e3';names=['Sign33MacroPrefixCarry03','Sign33MacroPrefixGsmall','Sign33MacroPrefixTheta','Sign33MacroPrefixGlarge'];objects=['5baddbffb05ddaabe7a2e2cec845380a3e0d642f9105d0569c441cefc78722aa','c5f5b65538743b2bd08f5e7e5dd1cc8fd95bef8e48a46801c303c53598ed230d','4897155b8bca501868fab555b6b1344ca955c985b4e007b4dc200d4ed2aca1d3','1887baa3203c288e248f8ee85eb0af794de72272dbde1c039a8774ebc4735e2f'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d8_B','d9_B','d9_b'],['prefix_g'],['prefix_theta'],['prefix_G']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroPrefixCarry','15d0497db6a70ec6bd4d9d3299aba42ef4484c9363ed61824b32093e1b74743e') if i==0 else (names[0],objects[0]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroPrefixGroup03.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-prefix-group03-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='079e4d2142ac28ef625d69b856cdadb8ccfcca23e6631d64a6361e548e9d4a60';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':27321,'stages':4,'guard_slots':400,'overlay_links':1067,'scope':'symbolic short-prefix B and b carries and g/theta/G only; no output equality'},indent=2,sort_keys=True))
