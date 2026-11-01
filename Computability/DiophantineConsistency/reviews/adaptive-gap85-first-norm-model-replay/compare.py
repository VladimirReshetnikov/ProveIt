#!/usr/bin/env python3
"""Compare two focused first-factor replays and their guarded direct candidates."""
from pathlib import Path
import hashlib,json,os,shutil
D=Path(__file__).resolve().parent; A=Path('/tmp/gap85-first-norm-model-ch_klt4z');B=Path('/tmp/gap85-first-norm-model-ld00gbt2');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
a,b=[json.loads((p/'state.json').read_text()) for p in (A,B)];assert a['status']==b['status']=='PASS' and A.resolve()!=B.resolve()
assert a['provider']==b['provider'] and a['boundary']==b['boundary'] and a['anchors']==b['anchors'] and a['checks_sha256']==b['checks_sha256'] and a['overlay_hash']==b['overlay_hash'] and a['overlay_entries']==b['overlay_entries']
assert len(a['candidate_guards'])==len(b['candidate_guards'])==400
for p,s in ((A,a),(B,b)):
 assert all(Path(k).is_file() and H(k)==v for k,v in s['anchors'].items())
 for path,row in s['candidate_guards'].items():
  if row is None:assert not os.path.lexists(path)
  else:assert Path(path).is_file() and str(Path(path).resolve())==row['realpath'] and H(path)==row['sha256']
 assert H(p/'src/DiophantineConsistency/AdaptiveGap85FirstNormModelChecks.lean')==s['checks_sha256']
 for row in s['records']:
  n=row['module'];assert row['exit']==0 and H(p/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and H(p/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'] and H(p/'logs'/(n+'.log'))==row['log_sha256']
  assert H(p/'logs'/(n+'.before.deps'))==row['deps_sha256']==H(p/'logs'/(n+'.after.deps'))
assert a['records']==b['records']
def normalized(s,p):
 return {k.replace(str(p),'${RUN_ROOT}'):v for k,v in s['candidate_guards'].items()}
assert normalized(a,A)==normalized(b,B)
for root,label in ((A,'author'),(B,'peer')):
 shutil.copyfile(root/'state.json',D/label/'state.json')
 for p in (root/'logs').iterdir():shutil.copyfile(p,D/label/p.name)
 shutil.copyfile(root/'src/DiophantineConsistency/AdaptiveGap85FirstNormModelChecks.lean',D/label/'checks.lean')
receipt={'status':'MATCHED_PASS','roots':[str(A),str(B)],'state_sha256':[H(A/'state.json'),H(B/'state.json')],'rows':a['records'],'candidate_paths_each':len(a['candidate_guards']),'parent_objects':a['parent_project_object_count'],'overlay_entries':a['overlay_entries'],'overlay_sha256':a['overlay_hash'],'comparator_sha256':H(__file__),'scope':a['scope']}
(D/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print('MATCHED_PASS',len(a['records']),'rows',len(a['candidate_guards']),'candidate paths',flush=True)
