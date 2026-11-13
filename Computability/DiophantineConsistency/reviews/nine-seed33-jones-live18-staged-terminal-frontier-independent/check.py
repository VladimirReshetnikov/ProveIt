#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-live18-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-live18-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='a0e202c47a4150d11099175971293d7d28c55dda2d380cfc2a7142c6e6f57e13' and sha(A/'outer-terminal-author-record.json')=='0f82de19f64a84c3d082e0db11e7645a03484b3dfae92451c7937cead767b6fc';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(71998,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1082 and s['runner_sha256']==sha(P/'run.py')=='4a379a90b42ad4b154d51564baca9c1d6fd547aba345088aae95002040b3bd8e';names=['Sign33MacroLive18Group01','Sign33MacroLive18Group02','Sign33MacroLive18Group03','Sign33MacroLive18Group04'];objects=['9ad348b1432ec9acb52c84a5605cf91131d04c1c4b7f8470715298eb582d99d1','8d4d912136b18a8d46b5904d3c1d8127e5fbafc40d62ffb25ef09a63c094b004','3fb6663a5d3070e902df9e95f4accd0058a7ada288923837f0c1464273388364','05ef726ab4c0aecb12d36ba7a0309a8875e335a387ebf4ea0810572beb9df0ec'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d18_b_carry','d18_N_carry','d18_g_carry'],['d18_G_carry','d18_R_carry','d18_h_carry'],['d18_s_carry','d18_w_carry','d18_phi_carry'],['d18_i_carry','d18_j_carry']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroRankSymbolic','b03354a0d7e2d662f5da26cd1a08adf15808912145b1d3a39f0c907518979a6f');v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroLive18.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-live18-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='255f78fa1e3467fa8910ea75623d8d5aa7fb2670da0684874c41aad006c50353'
up=D/'reviews/nine-seed33-jones-prefix-rank-symbolic-terminal-frontier-independent/check.py';assert sha(up)=='46208fc12365d384df197e33d4d15bb23391243eeebfe3bfe69cc5e700759c5b';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':71998,'stages':4,'guard_slots':400,'overlay_links':1082,'scope':'symbolic d18 live-entry carries only; no output equality'},indent=2,sort_keys=True))
