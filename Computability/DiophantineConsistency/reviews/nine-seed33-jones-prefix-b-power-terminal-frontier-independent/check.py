#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-b-power-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-prefix-b-power-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='4e9204d20463a3a99e7fb433fe9fe1b682513370a4697cb19ed3cb6f99ae78e6' and sha(A/'outer-terminal-author-record.json')=='c95bffd02c4adff3b6cae0d0eef5bacf90ccdbb7a0eee7d191c01f4caf45fbc6';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(91659,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1074 and s['runner_sha256']==sha(P/'run.py')=='e5e4ccd0a1db7b188596f9148d4fc13ff2b44950a45d6b05f9aa802647236107';names=['Sign33MacroPrefixBPower'];objects=['0abadc08a4ba54e39c9404a8bcffc4b9a742d33333b4c1cefbbf13e69252267f'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d10_B_eq_b_pow']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroPrefixCarryOthers','961c7686cc74a48cf3d4a1515690282a94d9869a904a89407c3d373113954dce');v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroPrefixBPower.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-prefix-b-power-prelaunch-frontier-independent/check.py';assert sha(review)=='1ac176e3a9d25094bdf883ed87efd3bee1f53606be0bde239960255522c82f13'
up=D/'reviews/nine-seed33-jones-prefix-group06-staged-terminal-frontier-independent/check.py';assert sha(up)=='01cb597e9419c90fd4377684442e9d55b7684bdef93b42f7ee5c94c35fb9045a';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':91659,'stages':1,'guard_slots':100,'overlay_links':1074,'scope':'symbolic d10 B=b^5 short prefix only; no output equality'},indent=2,sort_keys=True))
