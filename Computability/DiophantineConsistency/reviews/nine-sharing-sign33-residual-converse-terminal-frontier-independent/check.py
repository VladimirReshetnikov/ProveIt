#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-converse-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-residual-converse-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='d462e47723cb4ecee4963517244d1eb0ec23d532ca772795eea35a8a3633cd8c' and h(a/'outer-observation.json')=='293d6c7fccf7be7ac8e4c4c5915c2c0e43545cd75d7ec9c7f51e177df0bbdd2e'
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(2884,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==9
objs=['3906f691113b2b66869a2415221f056caa0c1f252c9f536c1291dd74b1ea3845','4d7b01a63f1679110bdc1863d90f1a6313a8e023bdb037e4b90db7cebd5108ae','6bd35dc7640a5149e76a6262ba881ff9156e54073c461a1658ab48cb96c84f96','1e58e308bd16a83b74c659e494cdd2e23d72c63d99f39580622f8897610310fd','af4635f4501ba704ec9a6c6de80d5734b17802910c1552bf3fde57d0007f598b','d4faf9dba5ac82428eafe548dd06657f6a5758e3f05e54ac94f0f5113ca2be0a','ebc2e6e3a9125c2d9ee6cc35ee9ababcab480116d467f91546db891afe53191d','338703c8fc84e668d055c33e88058f125eab8817c2de8f15afa1e4b4ac6b9648','b8ca561a903d941caadfc8cdd1dd05d7ba25f746e87a1e05b6cb26ce412d2272'];warnings=[3,4,4,4,1,0,4,4,0]
for i,(r,obj,w) in enumerate(zip(s['rows'],objs,warnings)):
 n='Sign33ResidualConverse%02d'%i if i<8 else 'Sign33ResidualConverse';assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert log.count('warning:')==w and log.count('warning: Variable name')==w and 'error:' not in log and 'sorryAx' not in log
 t='residuals_zero' if i<8 else 'seed_zero_of_all_cuts';assert re.search(r"'DiophantineConsistency\."+n+r'\.'+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 expected={'Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8'} if i<8 else {'Sign33ResidualConverse%02d'%j:objs[j] for j in range(8)}
 for mod,sha in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
 assert len(r['direct_guard'])==(100 if i<8 else 450)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1183
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':2884,'stages':9,'reports':9,'warnings':sum(warnings),'direct_guard_slots':1250,'overlay_links':1183,'scope':'AllCuts to seed zero on one valuation with four casts; no Lean replay'},sort_keys=True,indent=2))
