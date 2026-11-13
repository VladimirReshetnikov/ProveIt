#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-rank-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-prefix-rank-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='6ffd2a764e89ed1f75aa9ea0f6e934bfd385450ddf505f838f226d68470eb6db' and sha(A/'outer-terminal-author-record.json')=='e2b321a2d7dff0c25689c4c5a76a4f8a78046641d48cefe37da355bd4e31152d';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(74994,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1074 and s['runner_sha256']==sha(P/'run.py')=='96108a0b7ba16b87ba6fe17e85d69f279d56f19729cd27c70b0b9b08c25d1307';names=['Sign33MacroRankRaw','Sign33MacroRankCarry'];objects=['f63079c9cae648deeb2d063f472af4249a0cfd4438210787e3a6898aa9899650','fa5cbfb6529eef987495c023d5b4831d57566704f25251df9a1251870179f7df'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['Sign33MacroRankRaw.d11_rank_raw'],['Sign33MacroRankCarry.d11_rank_carried']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==([150,100][i])
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 expected=[('Sign33MacroPrefixCarrySums','7c11057ee7e9f5b201f8932d3c2347d69722836dc1aa7c6d71474abf5d391988'),('Sign33MacroPrefixCarryOthers','961c7686cc74a48cf3d4a1515690282a94d9869a904a89407c3d373113954dce')] if i==0 else [(names[0],objects[0])]
 for mod,h in expected:
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-prefix-rank-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='43aa49c48a92c876d02b167ec856df1e0dbb35a31067d3d1188d7789feff1d54'
up=D/'reviews/nine-seed33-jones-prefix-group06-staged-terminal-frontier-independent/check.py';assert sha(up)=='01cb597e9419c90fd4377684442e9d55b7684bdef93b42f7ee5c94c35fb9045a';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':74994,'stages':2,'guard_slots':250,'overlay_links':1074,'scope':'symbolic d11 raw and carried rank only; no output equality'},indent=2,sort_keys=True))
