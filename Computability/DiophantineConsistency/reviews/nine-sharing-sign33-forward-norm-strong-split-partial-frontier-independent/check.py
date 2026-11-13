#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-strong-split-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-norm-strong-split-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'69e89463a9efabe2e2e3bf2715a1b3064c8403e3fdf4ea75311eda6eed8595ca','Sign33ForwardCoordinate22-compile.txt':'13abeee606a17b47c0d106a51190e284e914802b1f66ad6970cff2baef36cde3','outer-observation.json':'e7317041058ee88c2047bb7d19412e1018d6edfffe3756d63230d0e58d1a9435'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['exit_code'])==(4849,1)
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==2
names=['Sign33ForwardNormStrong38','Sign33ForwardCoordinate22'];objects=['396c5de6c405053ee4d923b7f2391ae37f83cd9c10e054f689a7c17a9eb9465b','6bf0ed0ce4b7b853fb5d741b16bb30fefc2556fa3552a3a80699e5d97cab7cfd']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 if i==0: assert r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h
 else: assert not r.get('object_sha256') and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==(1 if i==1 and phase=='compile' else 0) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text()
 if i==0: assert re.search(r"'DiophantineConsistency\.Sign33ForwardNormStrong38\.strong_terminal' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log) and 'error:' not in log and 'sorryAx' not in log
 else: assert 'maximum number of heartbeats (200000)' in log and 'sorryAx' in log
 expected=({'Norm38ReferenceTerminals':'66a0624ab8ec394bffc1f65a905d3362f45ae4201a31b7997d4f2baab390f957','Norm38ReferenceFieldsAll':'3f7e3aea0ca0fa2c9700d128fd6d3a563a2345a0d61b81bcd0d87478c98b2dfd','Norm38ForwardGatesAssembly':'70dfab106e1db73ef99b1633f42aebab140af2cb111b58437f5b1e186f91d685','Norm38ForwardPrefix':'aeb6bfe74b17c695e41303bcb9f98cc5a60cb53d33774c03a84b71839d71a25f'} if i==0 else {'SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b'})
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==(250 if i==0 else 100)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert len(s['overlay_links'])==1194
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert not (a/'survey-after.json').exists()
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_AUDIT','author_recorded_outer_session':4849,'stages':2,'scope':'stage1 conditional terminal success; stage2 heartbeat failure, stages 3–5 unrun, no Lean replay'},indent=2,sort_keys=True))
