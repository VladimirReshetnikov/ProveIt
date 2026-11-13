#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-seed-squares-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-seed-squares-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='2f67af16b90778c2ce3c2ded36bf6ae2ef4239b36426cb359b99e550c4f140eb' and H(A/'outer-result.json')=='fbba289af465205a52d9e8df706e01d30895585e247a6e1c66379242970a6b5d';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(78148,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1057 and s['runner_sha256']==H(P/'run.py')=='37f082f9de588a448e3d6af489180aa6aef64a5836390c7feb7a3eb6cf94557c';names=['SharingSeed26Sextic','SharingSign26Squares'];objs=['49d762d74de47777373cf5bc09122915cfbf25e29e0adbcf020d5e6ece8e713d','49bddc37c95ec053d290fc8314dc7cea089f4cce33baec24ee000fc44d573eb3'];pins={'NineFreshJones':'9960f8baa9c5a058d8d472ce1600742bc53fa0030ee78add105b17744912d0df','SharingSign33Squares':'48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42',names[0]:objs[0]};m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i==0:assert not log
 else:assert "'DiophantineConsistency.SharingSign26Squares.seed_zero_iff_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-seed-squares-prelaunch-frontier-independent/check.py';assert H(pre)=='f6a1ff351b169047691564df54bac4a3ca69f25990ff4e2cd11d55f8a0074425';up=D/'reviews/nine-sharing-sign26-sextic-lean-draft-frontier-independent/check.py';assert H(up)=='dd7245fdd987b83e21e4fa2462db16213921dc758ad528248a2f4676b3cbddd9';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':78148,'stages':2,'guards':250,'links':1057,'scope':'sign26 symbolic seed and 17-row square-sum extraction only; no gap bridge'},sort_keys=True,indent=2))
