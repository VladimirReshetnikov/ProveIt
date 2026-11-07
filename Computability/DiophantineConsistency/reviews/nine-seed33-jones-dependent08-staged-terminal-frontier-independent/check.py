#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent08-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-dependent08-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='3a068e06a3ca8fc3c246a846037280fc84f558244dc456677c097bd9ee8e0c6d' and sha(A/'outer-terminal-author-record.json')=='4f61993c396c9fc4bd4cff6a8ffb47375e392f5dc88c90890ac387cc8919f000';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(78864,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1110 and s['runner_sha256']==sha(P/'run.py')=='eb35b873ef5d9fef7e4b4e585cba5044d466d119d0e1deb24313d45af00455cc';names=['Sign33MacroDependentBdCd','Sign33MacroDependentDmKc','Sign33MacroDependentOutput'];objects=['9a4cb929d4d26042fca68d900cad0442893b67bc37b17cc2c57e1edad9c88106','405792555e97d6dff1e6f1a2c9b309d14b17b97b00d4df2a0a806fe21815f7d4','36c16fb1daf0dcde1169dfb9468f2657f4d6e48fcae7c29c4155b84c6a65ffe3'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['prefix_Bd','prefix_Cd'],['prefix_Dm','prefix_Kc'],['prefix_T','prefix_output']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroDependentV','f42c741c3a2206f367c1c7d69b92af2a726d5520d64eae06ddb31dcebe08f789') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroDependent08.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-dependent08-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='a497396d0b04cb60d26b76a8474e9c930dfb2c22f9584bb7b47cbe2376db349f'
up=D/'reviews/nine-seed33-jones-dependent07-staged-terminal-frontier-independent/check.py';assert sha(up)=='f872f186a20f209db0c5df360da3c4ecbdd0d7788f2f6da775fc6e062d00459c';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':78864,'stages':3,'guard_slots':300,'overlay_links':1110,'scope':'d40–d45 immediate local prefix equations only; no full output semantic equality'},indent=2,sort_keys=True))
