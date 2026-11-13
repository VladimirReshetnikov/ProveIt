#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-source-import-diagnostic';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-source-import-diagnostic-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='976a088a5a3c339cf0236dde79403fa059c12a5c24d438c11d7e3b747a7ee87f' and H(A/'outer-result.json')=='9bf4ec575c356aebde716c2d0349274759039eb349846be5e31a50ac6a04c6db';s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='PASS' and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(43630,0) and o['retained_state_sha256']==H(A/'state.json') and len(s['rows'])==3 and len(s['overlay_links'])==1312 and s['runner_sha256']==H(P/'run.py')=='1c535471f4e526c19051c88a4a7e2d67e7c391fb437f1cf934d5382351798227'
names=['Sign28ImportCons','Sign28ImportSource','Sign28ImportBoth'];objs=['6a3a8ae5521398e7b052d2cbb548e0835e8e45fd03b656923ac059b4d18e2de2','3fbce93b6fca8878ac994787a833babcd767c481363b44a52c92720e3596c743','acbfce12da1482b362e10c5cc61c7cc28f86759d18f4ae4f9941104281ab657e'];imports=[['Sign28CurrentConsIff'],['Sign31CurrentSourceIff'],['Sign28CurrentConsIff','Sign31CurrentSourceIff']];pins={'Sign28CurrentConsIff':'2f7b33d5954dbc16bc528c98a3758954232304ad23f1121366881e307d74100b','Sign31CurrentSourceIff':'731041e2ed7302a0e2cb9fc0b8264be3195cd320ef6ccde407239ba57cd3d334'};m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,100,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'] and H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 assert (A/f'{n}-compile.txt').read_bytes()==b''
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in imports[i]:
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==pins[mod] and r['direct_guard'][v['path']]=={'sha256':pins[mod],'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-source-import-diagnostic-prelaunch-frontier-independent/check.py';assert H(review)=='ea0c79243b2fc89a6ef66392c1cb946e6622eae2b1f521d74e582bdcf38d35d7'
for survey,h in [('partial-survey.py','462acee066ec0a45fb30b682cc7d435a0b4b1414b9f8129c6f326ca3049ded8e'),('union-survey.py','a2f88678529dfef74f0f93aebf5b9e62ee0830842571089b48e91f646b91ab12')]:
 p=P/survey;assert H(p)==h;subprocess.run([sys.executable,'-I','-S','-B',str(p)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':43630,'stages':3,'guard_slots':350,'overlay_links':1312,'scope':'declaration-free import-only checks; no source theorem or cause diagnosis'},sort_keys=True,indent=2))
