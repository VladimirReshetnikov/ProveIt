#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-seed-current-source-retry01';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-seed-current-source-retry01-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'08353455cb5a8e98b891b8bd15e5717c345eec7979f93c01dee4036823f2c783','Sign33CurrentSeedSourceRetry-compile.txt':'18886bf05639ab7049b780214059ae3dd64228a0839095332c2d41b1be83d78f','outer-observation.json':'439069ee320ec2fa68dd0bee068165b3c70d19dc4d9fcbf2d5d9f1046934489e'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['numeric_exit'])==(82810,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Sign33SourceFourCasts','Sign33CurrentSeedSourceRetry'];objects=['f6704f1108ad8260886c3c011d24b2b1de1826e88efad1eac58d776d3c4b6d43','0be588190cf45140471a6cca9c58a1246e50313fa81b9e80f1370ee1d94ea009']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'error:' not in log and 'sorryAx' not in log;warning_count+=log.count('warning:');theorem='seed_implies_source' if i==0 else 'current_seed_implies_source';assert re.search(r"'DiophantineConsistency\."+n+r'\.'+theorem+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 expected=({'Norm38FourVariablePorts':'507e42e05050f66b1ee65be5826cac20bab0da1484c95a9f7964e4844e0fd68e','Sign33SeedSource':'d1575bc682b709f677efb2a33b562886e87d8b96f384f23a73f55d8b7933fa77'} if i==0 else {'Sign33SourceFourCasts':objects[0],'Norm38CurrentPort0':'0d5bc92d8592aa838671b36237f28b8bcca9bbdfceaf22877f99613d8ea55c43','Norm38CurrentPort1':'6429224b975688f1407395a7285c68fc716dd253a4bb11d2bdd175773ec30d86','Norm38CurrentPort2':'864dcedb4ccedd7af39f7704b999570b908a7f25b58519c75b0956e45f6a1eb2','Norm38CurrentPort3':'507e816bc8faf4b38f2e17a06dd15e67e9f1307e769b19cb776db17274eff57c'})
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==(150 if i==0 else 300)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert warning_count==0 and (a/'Sign33CurrentSeedSourceRetry-compile.txt').read_text().count('warning:')==0 and len(s['overlay_links'])==1218
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':82810,'stages':2,'reports':2,'warnings':0,'direct_guard_slots':450,'overlay_links':1218,'scope':'current seed zero implies shifted current source zero; no Lean replay'},indent=2,sort_keys=True))
