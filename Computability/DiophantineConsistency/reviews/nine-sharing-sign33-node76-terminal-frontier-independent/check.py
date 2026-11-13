#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-node76-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-node76-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'b6ea4c9b344d3d941803c224ff945d45f5783894e38eba37ab81bf3e68b61536','Sign33ReferenceNode76-compile.txt':'476c65742b465973a244eadd5c44a25261b935cfb728fb2ad30e10312335ca46','outer-observation.json':'98bb3e33d650bc6d4d1a24fdd3137f544b75ab4b48dff3cfa56cdd1b074e4043'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['exit_code'])==(25834,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Sign33StaticNode76','Sign33ReferenceNode76'];objects=['7c622ce54abd71af4d2c1c38a8e9808605480ea023312f3b6ea799654a42579b','62b5b7e2edb65010dc4c4eba34aac7c6a362b6e7827129485f0dbd6458057b5c']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'error:' not in log and 'sorryAx' not in log;warning_count+=log.count('warning:');theorem='node76' if i==0 else 'reference76';axioms=r"\[propext,\s*Classical.choice,\s*Quot.sound\]" if i==0 else r"\[propext,\s*Quot.sound\]";assert re.search(r"'DiophantineConsistency\."+n+r'\.'+theorem+r"' depends on axioms: "+axioms,log)
 expected=({'Norm38ReferenceTerminals':'66a0624ab8ec394bffc1f65a905d3362f45ae4201a31b7997d4f2baab390f957'} if i==0 else {'Norm38ReferenceFieldsAll':'3f7e3aea0ca0fa2c9700d128fd6d3a563a2345a0d61b81bcd0d87478c98b2dfd'})
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert warning_count==0 and (a/'Sign33ReferenceNode76-compile.txt').read_text().count('warning:')==0 and len(s['overlay_links'])==1194
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':25834,'stages':2,'reports':2,'warnings':0,'direct_guard_slots':200,'overlay_links':1194,'scope':'node76 static and reference identities; no Lean replay'},indent=2,sort_keys=True))
