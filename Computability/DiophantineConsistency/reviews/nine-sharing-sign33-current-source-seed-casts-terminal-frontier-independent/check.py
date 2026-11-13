#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-source-seed-casts-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-source-seed-casts-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'c91c2cf8a14bd68341d5c80c270c8ee8c4afae9ead9e5dccf242a8d346368140','Sign33CurrentSourceSeedCastFree-compile.txt':'93badfe08739179ca29029b1dd668fa7980cb2eda8fccb573fd6e9b3fb09d70c','outer-observation.json':'716a89c3be494106a7db8a501b23751f0a03cf06eb2c7b814d0d451826941e1c'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['exit_code'])==(68461,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Sign33SourceSeedFourCasts','Sign33CurrentSourceSeedCastFree'];objects=['eb75e887a1e036f7e876bdfca6d7cfe0b93b765e7769caa78125e2b40a23ea7e','796fd8b523c9ab3669d09ecf874f2bbe96318c56c90dea586d83e87b2cfd0d77']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'error:' not in log and 'sorryAx' not in log;warning_count+=log.count('warning:');theorem='source_implies_seed' if i==0 else 'current_source_implies_seed';assert re.search(r"'DiophantineConsistency\."+n+r'\.'+theorem+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 expected=({'Norm38FourVariablePorts':'507e42e05050f66b1ee65be5826cac20bab0da1484c95a9f7964e4844e0fd68e','Sign33CurrentSourceSeed':'df54a0aff1642e5a1fdd46e7c191041917aa276dfbb167b10da5de586ef134c5'} if i==0 else {'Sign33SourceSeedFourCasts':objects[0],'Norm38CurrentPort0':'0d5bc92d8592aa838671b36237f28b8bcca9bbdfceaf22877f99613d8ea55c43','Norm38CurrentPort1':'6429224b975688f1407395a7285c68fc716dd253a4bb11d2bdd175773ec30d86','Norm38CurrentPort2':'864dcedb4ccedd7af39f7704b999570b908a7f25b58519c75b0956e45f6a1eb2','Norm38CurrentPort3':'507e816bc8faf4b38f2e17a06dd15e67e9f1307e769b19cb776db17274eff57c'})
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==(150 if i==0 else 300)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert warning_count==0 and (a/'Sign33CurrentSourceSeedCastFree-compile.txt').read_text().count('warning:')==0 and len(s['overlay_links'])==1232
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':68461,'stages':2,'reports':2,'warnings':0,'direct_guard_slots':450,'overlay_links':1232,'scope':'concrete port current-source to 33 seed; no Lean replay'},indent=2,sort_keys=True))
