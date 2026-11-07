#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-current-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-current-iff-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='5069e81055514352e39b50d2bf4aff5ce57aee038213b11ac9cef6a000b742b9' and sha(A/'outer-result.json')=='867cef5cc386b0860b3a755d04bc73dc2b32e92af8e15019450bc78355535233';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(59009,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1072 and s['runner_sha256']==sha(P/'run.py')=='88bf40031a8d22e658eef74136c7dc75c5f0e65c29d52d66e4136091510fda53';names=['Sign28CurrentSeedIff'];objects=['21e5019d1429b95202aee5b03c2a422b09f7eb28876651fdd5f5a8f651292827'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign28SeedExistential','f8b2788e3395c755ce1efa95773af9c3e8d564d01a21fd45bb52a7610ecdcbe4') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 v=r['dependencies']['DiophantineConsistency.CurrentKernelData2011'];assert v['sha256']=='95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896' and v['realpath']=='/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/CurrentKernelData2011.olean' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in [(f'Sign28CurrentSeedIff.{x}','[propext, Classical.choice, Quot.sound]') for x in ('port0','pointwise','exists_same_input')]:assert f"'DiophantineConsistency.{th[0]}' depends on axioms: {th[1]}" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-current-iff-prelaunch-frontier-independent/check.py';assert sha(review)=='09b1324515ae26eb9edf2f3be3b892461d59f68b0ccdb2a4082c9aa52507f13d'
review=D/'reviews/nine-sharing-sign28-seed-iff-terminal-frontier-independent/check.py';assert sha(review)=='21864a3d4163554dac9e77a3530c699b5b1130a4afe1ee05b5f22a7def12d313';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
survey=P/'port-survey.py';assert sha(survey)=='15b06192778ba22a020e656fe6e2937f4653d60978ff87606daebe1b39d03a98';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':59009,'stages':1,'guard_slots':150,'overlay_links':1072,'scope':'current ports; sign28 pointwise and same-input existential iff sign31 in IΣ₁; no source/iPRA composition or JSON/degree binding'},indent=2,sort_keys=True))
