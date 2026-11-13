#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint31-41-e-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint31-41-e-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();n='Norm38MacroEValue'
for f,h in {'state.json':'4ccacbb59cfccda30d815bf30908839dccec208ba718094b0f027c4b0078fb19',n+'-compile.txt':'0da3db4ddc3844deb13c71b408e04a77c1446b5a77f0ed14723cfcaa29d13832','outer-terminal-author-record.json':'efd5a9912178947f81bfa11a3eeb2afc603c3a7b3f45870c7bf6b91499ef070f'}.items():assert sha(a/f)==h
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(64527,1);s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1247;r=s['rows'][0]
assert r['module']==n and r['source_sha256']=='d2510ec44441cdcd46e231343944659c876312a5798dc692b7fbfa368107e16f' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and not r.get('object_sha256') and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for phase,code in [('deps',0),('compile',1)]:
 x=r[phase];assert x['exit']==code and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(a/f'{n}-{phase}.txt')==x['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'Unknown identifier `prefix_i`' in log and 'unsolved goals' in log and log.count('sorryAx')==2
for mod,h in {'Norm38MacroDPath':'3eeb262b43d939b4af764a026281d006c0d7c05fecda77dba04fa28a9ced85db','Norm38MacroDependentE':'bc5eda5787bcabd4e9ae026819ab20bb299dfdd4aff76d59f7e3e3dc9fb85433','Norm38MacroJValue':'c6e4b69ed5e03ed41171bb6b85dada829f43625dc901b7de14f18305d8ac87a4','Norm38MacroLive18Group04':'d441a380efaacb979a20ed3370cfec35c900afd19d23eaa210b1b7d6bb76c143','Norm38MacroPrefixInputsB':'43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':h}
assert len(r['direct_guard'])==300
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert not (a/'survey-after.json').exists() and not (a/'Norm38MacroEPath-compile.txt').exists()
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':64527,'lean_exit':1,'scope':'unknown prefix_i and unsolved goal; error-contaminated reports; second stage unrun; no Lean replay','guard_slots':300,'overlay_links':1247},indent=2,sort_keys=True))
