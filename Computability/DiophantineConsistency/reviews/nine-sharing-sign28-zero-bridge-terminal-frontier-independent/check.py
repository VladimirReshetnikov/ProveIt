#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-zero-bridge-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-zero-bridge-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='acbc41b31a5082a4131041627e07781a8de3766247d926b47a87f4764a157b9b' and sha(A/'outer-result.json')=='a4369d6dd587ae88452c356a33c35809e68f04a8b09102064a41a3e4bb23488e';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(40266,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1066 and s['runner_sha256']==sha(P/'run.py')=='a7e7a3072162674d830383692a0ac8817abee0cc77ddd11741dded7c620353c8';names=['Sign28CoordinateRecover','Sign28CoordinateDrop','Sign28ForwardBridge','Sign28ReverseBridge'];objects=['07ada46da820c0e75a9d328c87d46a0839e019bb59f2de5c61932a0686a67a1c','dfe57e85ed02c925d1ab13bb6ab022df3765dad37889ffd7b7044edea5f16a35','1e4508c01b2a67289cddffa30e7ec55c328511e6e698993ecb3c627a57bbd1a0','5f7ce280d06fc119b5edd7256a309ab8e0291a4689e4c516a28d185b96442f01'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign28RemainingCuts01','0d25b68416f74f926585649e23e5fb9594f79b1f39e54eb10d7665b1f73763fc') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ([(f'Sign28CoordinateRecover.{x}_coordinate','[propext, Classical.choice, Quot.sound]') for x in ('x','c2','s2')],[('Sign28CoordinateRecover.lift_drop','[propext, Classical.choice, Quot.sound]')],[('Sign28ZeroBridge.old_rows','[propext]'),('Sign28ZeroBridge.forward','[propext, Classical.choice, Quot.sound]')],[('Sign28ZeroBridge.new_rows','[propext]'),('Sign28ZeroBridge.backward','[propext, Classical.choice, Quot.sound]')])[i]:assert f"'DiophantineConsistency.{th[0]}' depends on axioms: {th[1]}" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-zero-bridge-prelaunch-frontier-independent/check.py';assert sha(review)=='0869013ae1e042b79430da08352cad1a6c8e596fce69f627b9af507cf471b410'
survey=P/'first-cuts-survey.py';assert sha(survey)=='65bf351fcb60496ffa1a0c44ff1f8b9b7831646c2e30cb8e28235d7827ecb126';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=30)
review=D/'reviews/nine-sharing-sign28-remaining-cuts-terminal-frontier-independent/check.py';assert sha(review)=='d03a543e2971a3e71480a7c74e94cc7855cc6b9354c5aa01d5b8f6f4d0a558fb';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':40266,'stages':4,'guard_slots':400,'overlay_links':1066,'scope':'same symbolic ports and beta cast; sign28 forward lift and sign31 reverse drop in IΣ₁; no source/iPRA composition or JSON/degree binding'},indent=2,sort_keys=True))
