#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-first-cuts-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-first-cuts-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='82098b8677786e00940171383444350049b1b266251508e8fb138cb77e62d9b8' and sha(A/'outer-result.json')=='6d9d157ace0ff2aa298b648ba843d9b93d7dc04aa4a81c797950a75d99d94b26';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(55578,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1061 and s['runner_sha256']==sha(P/'run.py')=='6252e4b24b8b02c5605a45203be6dbfc0f67c89ad711e703e29186e96498733d';names=['Sign28FirstCuts00','Sign28FirstCuts01','Sign28FirstCuts02'];objects=['947a58d598f412347b6fdeb5b5412fe081c77e2f7ef7e9cbf3cd17fe48eb80e6','f56f7a6318e2101e5bd97a551b36717fe127f762b871693d6322afc2528c9cce','307de2d8391b7f65502dbc519b31256bca23675e20d0c08a429ddde43ec7eb12'];m=json.loads((P/'source-manifest.json').read_text())['rows'];rows=[['old_X_row','old_E_row','new_E_row','old_mainRoot_row','new_mainRoot_row'],['old_c2_row','old_Dc2_row','new_Dc2_row'],['old_normalizedS2_row','old_Na_row','new_Na_row','old_scaledNs_row','new_scaledNs_row']];triple=[['old_X_zero','E_eval','mainRoot_eval'],['old_c2_zero','Dc2_eval'],['old_normalizedS2_zero','Na_eval','scaledNs_eval']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[150,100,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 expected={'SharingSign28Squares':'942397e7cb222881da765f30804b2c4775673cba5a324cb58f0c51416d6c3f04','SharingSign31Squares':'51221006f98f8c12961936fcde04ae86c1d19f084c752d12dac79979255fda60'} if i==0 else {names[i-1]:objects[i-1]}
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();flat=' '.join(log.split());assert 'sorryAx' not in log and log.count('warning:')==[2,3,10][i] and log.count('not explicitly referenced')==[2,3,5][i] and log.count('This simp argument is unused:')==[0,0,5][i]
 for th in rows[i]:assert f"'DiophantineConsistency.Sign28FirstCuts.{th}' depends on axioms: [propext]" in flat
 for th in triple[i]:assert f"'DiophantineConsistency.Sign28FirstCuts.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in flat
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-first-cuts-prelaunch-frontier-independent/check.py';assert sha(review)=='1b08893351a479bc1d9fe1baf222cd4fa8fc7ae4e46b058d3ba6988aab596c49';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':55578,'stages':3,'guard_slots':350,'overlay_links':1061,'reports':'13 row [propext], 8 zero/eval [propext, Classical.choice, Quot.sound]','warnings':'10 unused binders, 5 unused simp arguments','scope':'three removed cuts and five affected survivor identities only, no full bridge'},indent=2,sort_keys=True))
