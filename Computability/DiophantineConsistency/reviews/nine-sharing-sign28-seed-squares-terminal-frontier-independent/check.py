#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-seed-squares-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-seed-squares-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='441410e9dba6c3df40f03fc04825b32b0aa637e021ea219d65d373fd150d602a' and sha(A/'outer-result.json')=='d646694a52855943ec600d6b459ef6483edc9bc9b8c23498b8beb3dfa9b0766d';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(64240,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1057 and s['runner_sha256']==sha(P/'run.py')=='6f1569c9926f8a76a428c2d007ee06515b10bbcd01d95e7eaebc050ceaa966fe';names=['SharingSeed28Sextic','SharingSign28Squares'];objects=['cbe6fe0a7b11251074e6795a020693513cec8f64b92bfcd58da2583c1b99ab4f','942397e7cb222881da765f30804b2c4775673cba5a324cb58f0c51416d6c3f04'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 expected={'NineFreshJones':'9960f8baa9c5a058d8d472ce1600742bc53fa0030ee78add105b17744912d0df'} if i==0 else {'SharingSeed28Sextic':objects[0],'SharingSign33Squares':'48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42'}
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 if i==0:assert log==''
 else:assert "'DiophantineConsistency.SharingSign28Squares.seed_zero_iff_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-sextic-lean-draft-frontier-independent/check.py';assert sha(review)=='7846f16aa633f3c366819b9693d9e89d3e1d1795165a4eb3cecfd91cce976d16';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':64240,'stages':2,'guard_slots':250,'overlay_links':1057,'scope':'symbolic-port seed zero iff all 19 residuals zero at same Fin29 valuation in IΣ₁; no bridge to sign31 or endpoint, no Lean JSON binding'},indent=2,sort_keys=True))
