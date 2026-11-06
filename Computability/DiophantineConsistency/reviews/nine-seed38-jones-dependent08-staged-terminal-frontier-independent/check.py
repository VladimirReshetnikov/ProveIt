#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent08-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-dependent08-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='3cbc8a506a81c3f7ef2a25e845049cb715623a36052ac55f7da0d952dae4cacf' and h(a/'outer-terminal-author-record.json')=='56952bf6e53bda8316728616ff8173a446baf9ad0e18c037b6b96fa69ded6cf1'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(57031,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3
names=['Norm38MacroDependentBdCd','Norm38MacroDependentDmKc','Norm38MacroDependentOutput'];objects=['c9f93896685c99df7b3dfdaf783d427f6a1150aeb48f70d56a9435597ce22940','9c6fa4a8df1d1376528fb8ae07ed1648572cf9e0534bb4d2d6cfc897cb157e59','39ae6b92258383e0505623a46c01a5ca71952561593a71090c0685508a7f8f58'];reports=[['prefix_Bd','prefix_Cd'],['prefix_Dm','prefix_Kc'],['prefix_T','prefix_output']]
for i,(r,n,obj,ts) in enumerate(zip(s['rows'],names,objects,reports)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroDependent08\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 mod='Norm38MacroDependentV' if i==0 else names[i-1];sha='93889388c58ac41b046d81d22bbdfd748ac726704bef2efe01ca6a132048d147' if i==0 else objects[i-1];dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha};assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1217
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':57031,'stages':3,'reports':6,'direct_guard_slots':300,'overlay_links':1217,'scope':'Bd/Cd/Dm/Kc/T/output immediate-prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
