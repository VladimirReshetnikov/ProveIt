#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-seed-squares-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign31-seed-squares-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='37ef748f7266db7b3e5cac072df191a2c5460a4d9842a54f33003c13c15473fb' and sha(A/'outer-result.json')=='bc5538f3c664a021ef77377e3a770e47bf75ed23636d07f5350f8b86293e53da';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(96916,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1057 and s['runner_sha256']==sha(P/'run.py')=='c23513b8d8b1257d87335f36fce98155caba6680577ea572c5ecda9fe1739f10';names=['SharingSeed31Sextic','SharingSign31Squares'];objects=['72ea075657b3ac99f0450a4fd31d2b5931bc9e842953b3f91badc3b34c143b3b','51221006f98f8c12961936fcde04ae86c1d19f084c752d12dac79979255fda60'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 expected={'NineFreshJones':'9960f8baa9c5a058d8d472ce1600742bc53fa0030ee78add105b17744912d0df'} if i==0 else {'SharingSeed31Sextic':objects[0],'SharingSign33Squares':'48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42'}
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 if i==0:assert log==''
 else:assert "'DiophantineConsistency.SharingSign31Squares.seed_zero_iff_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign31-sextic-lean-draft-frontier-independent/check.py';assert sha(review)=='4e48b606cf567b5ec6e61b5809f3f3461e3284f7486d2fb7b99b1462b27c5f33';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':96916,'stages':2,'guard_slots':250,'overlay_links':1057,'scope':'symbolic-port seed zero iff all 22 residuals zero at same Fin32 valuation in IΣ₁; no bridge to sign32 or endpoint, no Lean JSON binding'},indent=2,sort_keys=True))
