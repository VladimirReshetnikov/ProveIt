#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group02-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-prefix-group02-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='64adc92ea6a031a7054da32199c190b50e63ab4eb5046e4151dbd993f7e73b67' and sha(A/'outer-terminal-author-record.json')=='b1fd9afd93169f61f6286dcb542f34b90ac060430eb0434cf17ae50b0b8044de';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(7214,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1063 and s['runner_sha256']==sha(P/'run.py')=='4b0234adac6967a02a25fe98ed415f2a4c21dffb78371577b20d1052cfdc68d9';names=['Sign33MacroPrefixCarry','Sign33MacroPrefixE','Sign33MacroPrefixEll','Sign33MacroPrefixLambda'];objects=['15d0497db6a70ec6bd4d9d3299aba42ef4484c9363ed61824b32093e1b74743e','a56f7d3448740f9a1b926ba82c9da13a58c29ab54cd8175d1464978298f3959a','0ae3b42fce126754676f45a851c98f2aff6a679056db9a51e503ab60c2424026','ebf67b62c3686e73995a0708230f464de83eb11fc10d02b17bff34f642790666'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d4_B','d5_B','d6_B'],['prefix_e'],['prefix_ell'],['prefix_lambda']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroPrefixGroup01','d2295245406c44360fd6c219cbd16d5117b9566e855a2cf4e5e2352fdccfdbbf') if i==0 else (names[0],objects[0]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroPrefixGroup02.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-prefix-group02-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='34f11227c7e5bd0cb8f2fbd0357729e7a4743dcb00f94512da446e1cd3ed254a';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':7214,'stages':4,'guard_slots':400,'overlay_links':1063,'scope':'symbolic short-prefix B carries and e/ell/lambda only; no output equality'},indent=2,sort_keys=True))
