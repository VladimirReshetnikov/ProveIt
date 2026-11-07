#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent02-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-dependent02-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='5e4bb01a6e6e638335fe40d01bbaa8eb10e04fd43156ff8c8c37693186f64a17' and sha(A/'outer-terminal-author-record.json')=='6c6a7f38afee07e70a344a8632acb5381f717f5b1517addfd3f72c52af190781';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(90623,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1088 and s['runner_sha256']==sha(P/'run.py')=='04e098e11c26df54507915431e44f5364fcc0fd00e28ab0620d796e2b285eb62';names=['Sign33MacroDependentM','Sign33MacroDependentP','Sign33MacroDependentK'];objects=['b1dfcad99ce4808c6aa675c8c8ef7e7d842755595811b10ad29eba363d5f8862','c4d38fbc81e2386b0385138277d63145f115cde5cfe5ce9b49cd12d2bf5cb02c','d8702218c9633485b986a49cb9cb4308027648156649c3babd196f612f751174'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d20_R_carry','prefix_M'],['d21_U_carry','prefix_P'],['d22_R_carry','d22_h_carry','prefix_K']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroDependentY','14f9815d4dbf41a173a275175da5a02ac7b602c610135d0cbf1ba1ce2cb6ea8e') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroDependent02.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-dependent02-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='1e4add819ca6f0858c1a43910fc4d793288ecd92006b6a89cda602b45c548547'
up=D/'reviews/nine-seed33-jones-dependent01-staged-terminal-frontier-independent/check.py';assert sha(up)=='26cd23263872a52a78f345152c16d8e8dd20061c73f78cdd0b8f25d3ec39ad22';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':90623,'stages':3,'guard_slots':300,'overlay_links':1088,'scope':'local d21–d23 M/P/K prefix equations and carries only; no output equality'},indent=2,sort_keys=True))
