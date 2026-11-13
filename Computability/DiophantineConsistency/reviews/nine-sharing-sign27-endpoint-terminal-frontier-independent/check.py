#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-endpoint-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-endpoint-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='77629ee2c239ab54c47c27b84af88306cb040b4558e20d2679694576f9143f56' and H(A/'outer-result.json')=='052925b53111b5fae1e8abf4cfdce85c979e50244df83eb1d1d1ce9c1724f9ce';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(88387,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1344 and s['runner_sha256']==H(P/'run.py')=='7c9dec8f519e297f98283bd6409a1387526ceb6ecfd743f67165da2f3007c39b';names=['Sign27DirectNative','Sign27DirectStandard','Sign27DirectTranslated'];objs=['86e89788e683d8ec64d0f6d357129a747e8ae9918417799868c5e4310a22f996','1c54e59264dc771e4636feb44bced4fe7bf0895c5561653623b0c68fea6436fa','3a193bb3dea6b176b0c10628839229f9cb0ed698100e5fef8048b2e3dd2b0f8e'];ths=['native_equivalence','standard_equivalence','standard_translated_equivalence'];pins={'Sign27DirectPolynomialBridge':'67fffa115363264cc4181c667ff2a0667493b9327708f58e6e500f00e7d24bb3','IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684','IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19',**dict(zip(names,objs))};m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[150,150,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log and f"'DiophantineConsistency.Sign27DirectIPRA.{ths[i]}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign27-endpoint-prelaunch-frontier-independent/check.py';assert H(pre)=='35de350fd9124142ef5babda59042ecee761dd08d930cf72f00f4c660c13d701';up=D/'reviews/nine-sharing-sign27-concrete-polynomial-bridge-terminal-frontier-independent/check.py';assert H(up)=='67fac5489394738924d5023bd03b19624781cfc7f60c6fa2dc23bd404a8a8bce';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':88387,'stages':3,'guards':400,'links':1344,'scope':'native, standard and translated iPRA endpoints for direct Fin27 expression; no nine-variable or degree claim'},sort_keys=True,indent=2))
