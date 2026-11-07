#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-constructor-ell-retry02';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-constructor-ell-retry02-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'ac57f166f4da6cb14f928abd3914ed06a0178859c177836e107efd7e431fece8','Sign33ConstructorEllRetry-compile.txt':'b239a8c9cc4a1e951213d1698a8b9879f474f8564725c7e5094d17d2eda90984','outer-observation.json':'096b9e4c0060916554e305a5e0ab09149e57ed585827ca7c4d3576213a0dc411'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['exit_code'])==(71832,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Sign33AbstractProjection21','Sign33ConstructorEllRetry'];objects=['db224dccd2611215f9387b3122bb11f3ec55ed2e474f7d2f1060d362f2965d06','be7375726277bf550e39cfd39b20955b120c6febd748362e1a269c46072ad830']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 assert r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text()
 if i==0: assert all(re.search(r"'DiophantineConsistency\.Sign33AbstractProjection21\."+t+r"' depends on axioms: \[propext\]",log) for t in ('template','project')) and 'error:' not in log and 'sorryAx' not in log
 else: assert re.search(r"'DiophantineConsistency\.Sign33ConstructorEllRetry\.ell_of_core' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log) and 'error:' not in log and 'sorryAx' not in log and log.count('warning:')==1
 expected=({'Sign33AbstractTuple':'fa8ec17dc816676fcfa21edc6270fe24ba4231337653034b2d033ff5d60c5373'} if i==0 else {'Sign33AbstractProjection21':objects[0],'Sign33StaticNode30':'8d150d69ce5e2e75fa7e4722bda965d746678ebb1f5eca50a546332e8d3c974c','Sign33ReferenceEll':'0bc514b3781c16434a3360dd905fa32b0711491713f5b234f0dff0c482e9696d','Norm38ForwardGatesAssembly':'70dfab106e1db73ef99b1633f42aebab140af2cb111b58437f5b1e186f91d685','Norm38ForwardPrefix':'aeb6bfe74b17c695e41303bcb9f98cc5a60cb53d33774c03a84b71839d71a25f'})
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==(100 if i==0 else 300)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert len(s['overlay_links'])==1198
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':71832,'stages':2,'scope':'constructor ell identity, no Lean replay'},indent=2,sort_keys=True))
