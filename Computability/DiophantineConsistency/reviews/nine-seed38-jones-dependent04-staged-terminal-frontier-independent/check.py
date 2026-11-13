#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent04-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-dependent04-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='c62aae410c3531d4c405143553c4d5daa9d462c0563d419122968ed865a475dc' and h(a/'outer-terminal-author-record.json')=='187cb02ea13f4a9d4a8f571d31a3e91b2e390e0354aa42f7a6b7f08fb12c1d3b'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(26682,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3
names=['Norm38MacroDependentJ','Norm38MacroDependentQ','Norm38MacroDependentD'];objects=['bf9afeef4f54470a90af0dea2251e33e4b66c4b7518b47fb37b089a166e09bf7','a306bbaa1f89b688b9a99bcd7146fa0b989eb1c0574810c6197c7a518b461840','3fb3464ef223d9d0e7dc33fccd7d1845337aea9ccc9184c137e6664bc2026931'];reports=[['d27_A_carry','prefix_J'],['d28_W_carry','d28_C_carry','prefix_Q'],['d29_A_carry','d29_C_carry','prefix_D']]
for i,(r,n,obj,ts) in enumerate(zip(s['rows'],names,objects,reports)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroDependent04\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 mod='Norm38MacroDependentC' if i==0 else names[i-1];sha='8a69d181c2584313ff4add42d2197020e387b888cd676fbfa4dc465a305bd281' if i==0 else objects[i-1];dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha};assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1202
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':26682,'stages':3,'reports':8,'direct_guard_slots':300,'overlay_links':1202,'scope':'J/Q/D short-prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
