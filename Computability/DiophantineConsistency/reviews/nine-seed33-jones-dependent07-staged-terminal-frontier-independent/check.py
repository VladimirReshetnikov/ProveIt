#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent07-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-dependent07-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='3a8195d8b93a24093e10b7f2001be5ecb13bff674fe8447621d9c127d370303c' and sha(A/'outer-terminal-author-record.json')=='3c26d1a23ba2faf12e3c262589882d1c3cf9dd767a9510de06780a256da63844';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(70777,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==5 and len(s['overlay_links'])==1105 and s['runner_sha256']==sha(P/'run.py')=='ea482651d28a32a624d6937535e92c0504b358baf4adf6b2153e8f0df60ee736';names=['Sign33MacroDependentI','Sign33MacroDependentA0Early','Sign33MacroDependentA0','Sign33MacroDependentA1','Sign33MacroDependentV'];objects=['9c2f73b4a8d97fe02e9058bc6edb825998a8a6a4b955e5cb72177b3cca92bc0b','6d21ae7eba12affee1d2eebcff32ec1fc1c9589c8c4e23fe726b92db229f953b','2cbf54691d0430b46e6485ed18a3cbd542645537efb69bc4001d990f66b32f05','bec5da4c4f0e4aa767ffe019ba460e3e5f64645db1de0b1f408c78e5940091c7','f42c741c3a2206f367c1c7d69b92af2a726d5520d64eae06ddb31dcebe08f789'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d34_Gprime_carry','prefix_I'],['d28_P_carry','d29_K_carry'],['d35_P_carry','d35_K_carry','prefix_A0'],['d36_D_carry','d36_F_carry','d36_I_carry','prefix_A1'],['d37_A0_carry','d38_A1_carry','prefix_V0','prefix_V1']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroDependentH','5b5bf4045f0e4f151681765d3339d847559f324ee47ebc37fc046b120165ce01') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroDependent07.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-dependent07-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='a1c8cf1b5ba2042978fd3a29c24a211f60601d3e3ff33e77b32c01bb06773179'
up=D/'reviews/nine-seed33-jones-dependent06-staged-terminal-frontier-independent/check.py';assert sha(up)=='e001e3551bd9ae1ea7ffa32a4b247b6df6157e7156e20e5992913e6ca7d54f87';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':70777,'stages':5,'guard_slots':500,'overlay_links':1105,'scope':'local d35–d39 I/A0/A1/V prefix equations and carries only; no output equality'},indent=2,sort_keys=True))
