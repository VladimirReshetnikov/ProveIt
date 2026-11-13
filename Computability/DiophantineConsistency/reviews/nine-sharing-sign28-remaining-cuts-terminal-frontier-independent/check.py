#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-remaining-cuts-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-remaining-cuts-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='264fcf2c4635022f0e16e85fcaf5bf5bc7f06ddaf9a9749e3743f760399fde73' and sha(A/'outer-result.json')=='e259e7a66c37da70bb05a74490189e93a83c97c986ace8eabd039b6884fc36d5';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(53605,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1064 and s['runner_sha256']==sha(P/'run.py')=='5976532eabb710666179c4dcb52e1204f4403e964a32513fbd6b97ecb04a81b9';names=['Sign28RemainingCuts00','Sign28RemainingCuts01'];objects=['ddc0ea5e374c99c5399ef9379439c22306996059cac0d3885f3bcbc9bb22d207','0d25b68416f74f926585649e23e5fb9594f79b1f39e54eb10d7665b1f73763fc'];m=json.loads((P/'source-manifest.json').read_text())['rows'];total=0
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign28FirstCuts02','307de2d8391b7f65502dbc519b31256bca23675e20d0c08a429ddde43ec7eb12') if i==0 else (names[0],objects[0]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'sorryAx' not in log and log.count('warning:')==[13,8][i] and log.count('not explicitly referenced')==[10,8][i] and log.count('This simp argument is unused:')==[3,0][i];reports=re.findall(r"'DiophantineConsistency\.Sign28RemainingCuts\.(\w+)' depends on axioms: \[propext, Classical.choice, Quot.sound\]",' '.join(log.split()));assert len(reports)==7 and len(set(reports))==7;total+=len(reports)
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-remaining-cuts-prelaunch-frontier-independent/check.py';assert sha(review)=='7a229ba31376c22ef9b9e876d1979a467853f58db07d889657fa6b7778e3dda2';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':53605,'stages':2,'reported_evaluation_theorems':total,'warnings':'18 unused binders and 3 unused simp arguments','guard_slots':200,'overlay_links':1064,'scope':'q3 and 13 unaffected row identities; no assembled forward/reverse bridge'},indent=2,sort_keys=True))
