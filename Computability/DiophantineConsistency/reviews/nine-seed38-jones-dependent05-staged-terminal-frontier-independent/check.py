#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent05-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-dependent05-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='d665fd2f52809dd9543fa2f3c2221af93547c27e694a93074b99bdfad1b9641e' and h(a/'outer-terminal-author-record.json')=='d5d8429b9aaa06e6f29cdc7b5638754229f328aa68c5e4375aa2d4ddb13111ae'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(3030,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3
names=['Norm38MacroDependentIcarry','Norm38MacroDependentE','Norm38MacroDependentF'];objects=['7f2fa486d3339917f36dd43b1128d3e35eb106ef07ef86fb037b9604d450d029','bc5eda5787bcabd4e9ae026819ab20bb299dfdd4aff76d59f7e3e3dc9fb85433','a7700d99911c457d906075eccae9433ac825b8b9fc0df269c01bfd66426b2118'];reports=[['d24_i_carry'],['d30_i_carry','d30_J_carry','d30_C_carry','prefix_E'],['d31_A_carry','prefix_F']]
for i,(r,n,obj,ts) in enumerate(zip(s['rows'],names,objects,reports)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroDependent05\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 mod='Norm38MacroDependentD' if i==0 else names[i-1];sha='3fb3464ef223d9d0e7dc33fccd7d1845337aea9ccc9184c137e6664bc2026931' if i==0 else objects[i-1];dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha};assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1205
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':3030,'stages':3,'reports':7,'direct_guard_slots':300,'overlay_links':1205,'scope':'E/F short-prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
