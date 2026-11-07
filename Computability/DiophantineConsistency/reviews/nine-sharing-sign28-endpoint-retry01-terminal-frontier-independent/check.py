#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-endpoint-retry01';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-endpoint-retry01-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='547efa7338b312ff9996fd62ad23d4e9c613ab9eec16de5d3d6a731d55e895a3' and H(A/'outer-result.json')=='fb70684a6af3629310c74211edd105bb2fd892dca1ac641177c6612b34471a39';s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='PASS' and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(67030,0) and o['retained_state_sha256']==H(A/'state.json') and len(s['rows'])==3 and len(s['overlay_links'])==1326 and s['runner_sha256']==H(P/'run.py')=='0a40521beb44e494003b5f2fce44c2de6542439209852e0a1f33e41008cf93b8'
names=['Sign28DirectNative','Sign28DirectStandard','Sign28DirectTranslated'];objs=['3dbd7685049529ffae98bce417e33a848b98c959e75dce4e648594ed71f0d860','f22b688ad44af38bb60379de16f5d212e7509d49f40e30f643a45ca880b31915','83014e7e29e47ba1f9faba4afbbc32d770bc83bcec88735e9089923782382c80'];deps=[{'IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684','Sign28DirectPolynomialBridge':'211972881dab16d1bb9be9c457b18a0e48b698be5199bdf2918d781d5e06ab07'},{'IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19',names[0]:objs[0]},{names[1]:objs[1]}];ths=['native_equivalence','standard_equivalence','standard_translated_equivalence'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[150,150,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'] and H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod,h in deps[i].items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log and f"'DiophantineConsistency.Sign28DirectIPRA.{ths[i]}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-endpoint-retry01-prelaunch-frontier-independent/check.py';assert H(review)=='c576f4f46b237e1128e749d816d5fb5b230eebc2ed567292310bf0f89d9c0460'
framework=P/'framework-survey.py';assert H(framework)=='20bceb0b7631d230eac91deb2778690edb90a6d72c4af61a07e2bc4edc97c9a6';subprocess.run([sys.executable,'-I','-S','-B',str(framework)],check=True,capture_output=True,timeout=60)
review=D/'reviews/nine-sharing-sign28-concrete-polynomial-bridge-terminal-frontier-independent/check.py';assert H(review)=='636f8d20637997f460a9a64577ed3d61d1fdeffd26c6527031c5519f5647e4c5';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':67030,'stages':3,'guard_slots':400,'overlay_links':1326,'scope':'direct Fin28 native/standard/translated endpoints; no Jones/degree/JSON claim'},sort_keys=True,indent=2))
