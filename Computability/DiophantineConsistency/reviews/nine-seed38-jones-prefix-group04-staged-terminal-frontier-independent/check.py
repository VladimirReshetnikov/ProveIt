#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-group04-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-group04-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='b8a10144c1331d6eb06789d23eef0bd1713d6ebb1876449270216e6ff6e082c1' and h(a/'outer-terminal-author-record.json')=='59751fd7c4b8bb44145995eed7d580b2719c8f414d564c02e49661f96310694e'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(32987,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Norm38MacroPrefixInputsA','Norm38MacroPrefixInputsB'];objects=['ab8025bff041d6816025d2457dc12f9d5fa4e6072d399a8b8767d16bcbb2faf9','43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170'];reports=[['prefix_h','prefix_s','prefix_w'],['prefix_phi','prefix_i','prefix_j','prefix_t']]
for r,n,obj,rs in zip(s['rows'],names,objects,reports):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in rs:assert re.search(r"'DiophantineConsistency\.Norm38MacroPrefixGroup04\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 dep=r['dependencies']['DiophantineConsistency.Norm38MacroPrefixGlarge'];assert dep['sha256']=='b685399878adfa8efc0fae22b6f9793c1f74079b4266cfff15d86a6a25e89a06' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
 assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1178
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':32987,'stages':2,'reports':7,'direct_guard_slots':200,'overlay_links':1178,'scope':'short-prefix input values; no Lean replay'},sort_keys=True,indent=2))
