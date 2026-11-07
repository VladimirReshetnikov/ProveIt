#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-rankcode-link-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-rankcode-link-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='122f1c1ff6636be74805668ff4569906bb013488a5a1ff79957822757a86425a' and sha(A/'outer-terminal-author-record.json')=='580c4efe572c43a090457667f92cbbf9ba93e3af36e7d81da291de90af50d389';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(88667,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1076 and s['runner_sha256']==sha(P/'run.py')=='8494b29c8272e982c8d0cd37d8316d4261f7fd4543bc292f754dcffd606a6699';names=['Sign33MacroRankCodeLink'];objects=['a83b477c13eda000f27e7287eecaa2be404aba44c3c81b907cd4c05cf3017fec'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['rankRaw_eq_rankCode']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroRankCarry','fa5cbfb6529eef987495c023d5b4831d57566704f25251df9a1251870179f7df');v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroRankCodeLink.{th}' depends on axioms: [propext]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-rankcode-link-prelaunch-frontier-independent/check.py';assert sha(review)=='6c209b23c6d03a57169f20f965a28d194b2a19457ceb84eecd8efc0fd2385fb1'
up=D/'reviews/nine-seed33-jones-prefix-rank-staged-terminal-frontier-independent/check.py';assert sha(up)=='7cc0b0f7932a9cf16159160e0f7c8ed694bc11715e6f8daa8e7aca22d1879abd';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':88667,'stages':1,'guard_slots':100,'overlay_links':1076,'scope':'generic commutative-ring rankRaw/rankCode identity only; no output equality'},indent=2,sort_keys=True))
