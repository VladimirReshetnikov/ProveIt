#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-rank-retry01';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-rank-retry01-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='dbe29a56b76450013ea9a2b3ed01e6e1ba157c4d12dc34d1713eecb905ffb6ac' and h(a/'outer-terminal-author-record.json')=='c8dc406473804d0c45631c7fa9846414c8ec1382bec1ccc4ac5613d1dcd44fbf'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(11405,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Norm38MacroRankRaw','Norm38MacroRankCarry'];objects=['99db14ff62470a6cc251ef283fe403552fe2d38f1163f474867ae559727e00ca','60217f4104203c8fde8da56182d932e5382b9b7b118962b8f0a392dd799e6c89'];reports=['d11_rank_raw','d11_rank_carried']
for i,(r,n,obj,t) in enumerate(zip(s['rows'],names,objects,reports)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log;ns='Norm38MacroRankRaw' if i==0 else 'Norm38MacroRankCarry';assert re.search(r"'DiophantineConsistency\."+ns+r'\.'+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 expected={'Norm38MacroPrefixCarrySums':'789438afddf47cad95d8657dd0d029f284fa9d3a02dc99ab33275214ffe70eb2','Norm38MacroPrefixCarryOthers':'9cc1239aeeff42841ca5d2f71796aeb859846dcefd4992fce2417e879f804279'} if i==0 else {'Norm38MacroRankRaw':objects[0]}
 for mod,sha in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
 assert len(r['direct_guard'])==(150 if i==0 else 100)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1181
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':11405,'stages':2,'reports':2,'direct_guard_slots':250,'overlay_links':1181,'scope':'d11 symbolic rank node, not rankCode; no Lean replay'},sort_keys=True,indent=2))
