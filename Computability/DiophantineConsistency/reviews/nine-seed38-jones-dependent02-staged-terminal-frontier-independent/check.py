#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent02-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-dependent02-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='c841258f951de4fd36c66e3acb1aa31ba621eaa40020ef8764cb7dc448ec1746' and h(a/'outer-terminal-author-record.json')=='231c4749ae64ccd3c738abf94a7732f3c5db93e7c9b2a8386cd3ded0751ddc0f'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(75249,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3
names=['Norm38MacroDependentM','Norm38MacroDependentP','Norm38MacroDependentK'];objects=['81363f56b3ea598151f89eda0e9cce2bdeca9c7b2a989b20739059343eb72454','02d7d218dd922bd33bf7e8f6aad2533855fe157dbd3ea844b5111a335c9db964','54542c0eb712eb19b70ae07aef9308156edf7fc4311e177d00fb8181278a5f9d'];reports=[['d20_R_carry','prefix_M'],['d21_U_carry','prefix_P'],['d22_R_carry','d22_h_carry','prefix_K']]
for i,(r,n,obj,ts) in enumerate(zip(s['rows'],names,objects,reports)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroDependent02\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 mod='Norm38MacroDependentY' if i==0 else names[i-1];sha='eb28e13077c175963702682ff8501cb25c4036813d5d035c3574a9e605f516a9' if i==0 else objects[i-1];dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha};assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1195
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':75249,'stages':3,'reports':7,'direct_guard_slots':300,'overlay_links':1195,'scope':'M/P/K short-prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
