#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-remaining-cuts-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign31-remaining-cuts-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='d66a3325835ed8528959da207d94f7b6d6a61909695d2926e399333405e78a2b' and sha(A/'outer-result.json')=='16e8af505a8b05b4616629b415dc18f7317113d1f0ef3537a84fc8df06f99d70';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(98808,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1062 and s['runner_sha256']==sha(P/'run.py')=='870368fda93183ba99bbdd71db0e4957b412285c2b60694c2c608193791c290e';names=['Sign31RemainingCuts00','Sign31RemainingCuts01'];objects=['d23116ae51933da258c30bff6275ebcdca65253cc15ec3c4a53c4adaf408f79c','20c42c47ebfe30151e36dc51cfbfd2b4a993d4fd633eba6b7f7021570e033b9e'];m=json.loads((P/'source-manifest.json').read_text())['rows'];total=0
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign31FirstCut','491d5b244596b4051298ee640a3ec6cb827ca650febd3cf06c25749ee0637e74') if i==0 else (names[0],objects[0]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'sorryAx' not in log and log.count('warning:')==[22,15][i] and log.count('not explicitly referenced')==[16,12][i] and log.count('This simp argument is unused:')==[6,3][i];reports=re.findall(r"'DiophantineConsistency\.Sign31RemainingCuts\.(\w+)' depends on axioms: \[propext, Classical.choice, Quot.sound\]",' '.join(log.split()));assert len(reports)==10 and len(set(reports))==10;total+=len(reports)
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign31-remaining-cuts-prelaunch-frontier-independent/check.py';assert sha(review)=='6718836d3235a9f508b777cad8fb19499f7de7c0ae5e22d27ff489f4de015de0';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':98808,'stages':2,'reported_evaluation_theorems':total,'warnings':'28 unused binders and 9 unused simp arguments','guard_slots':200,'overlay_links':1062,'scope':'q3 and 19 unaffected row identities; no assembled forward/reverse bridge'},indent=2,sort_keys=True))
