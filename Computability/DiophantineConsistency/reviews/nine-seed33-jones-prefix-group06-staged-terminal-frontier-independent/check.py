#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group06-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-prefix-group06-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='40e9cd7f799a611b5a610a4d29254a2146c4ee264eaf5490b6bf3fae4915aaf5' and sha(A/'outer-terminal-author-record.json')=='58a80804087464f8912be5f4fca82c04ff449732a250b4153f297c55550b7a12';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(70623,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1072 and s['runner_sha256']==sha(P/'run.py')=='49bb6396d0128870498e2b83366daa0fc227251a9b2d7c87041fc670119c7a6c';names=['Sign33MacroPrefixCarrySums','Sign33MacroPrefixCarryOthers'];objects=['7c11057ee7e9f5b201f8932d3c2347d69722836dc1aa7c6d71474abf5d391988','961c7686cc74a48cf3d4a1515690282a94d9869a904a89407c3d373113954dce'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d10_e_carry','d10_ell_carry','d10_lambda_carry'],['d10_g_carry','d10_theta_carry','d10_B_carry','d10_b_carry']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroPrefixQNCarry','c35a2307d35050bac27cb469bb3acf21ecca0d94c925eb440b981eb8b258b50b');v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroPrefixGroup06.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-prefix-group06-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='1ab1614b2d0ac07d35f045ddad277ccf2a163a277e4ea1c07b7c37a54d15b9d4'
up=D/'reviews/nine-seed33-jones-prefix-group05-terminal-frontier-independent/check.py';assert sha(up)=='7a444e4e5047b43e23ca34177478b97bcf8a0ba41fe2e7c8bfa1e8467e6805c3';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':70623,'stages':2,'guard_slots':200,'overlay_links':1072,'scope':'symbolic d10 carry equalities to short prefixes only; no output equality'},indent=2,sort_keys=True))
