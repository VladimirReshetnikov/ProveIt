#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-five-norms-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-five-norms-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'748448e7eb40eff7b3ed5cbe716b8cd3baa167c7ecdab791615af859d2f8596c','Sign33LiftFiveNorms-compile.txt':'0c146bd9af23657d13d7ddd4df79f6f431fccb70520cb8d6806fd6cd8bec1dde','outer-observation.json':'0e7953ba1ccbfcbe8f457d40ce4d2e1bb2615fa60c7349b6b15aaf4bbfb6c672'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['numeric_exit'])==(37568,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==6
names=['Sign33LiftNorm'+str(i) for i in range(5)]+['Sign33LiftFiveNorms'];objects=['5218749d9d016f191e981cf57d96953131e87fc0f56f9635220bcd21890d06fc','c00f78b942e4a1cc36e0f4f12c29048be0d2c1427fa48abc043ab8ef8c4abb98','2553c7e1cfdfe29c353c1088568be8de62e5485540972f48b21e1e9f410e6464','d939355cdb3cc91bf593c05242e490b0b8be4f8dba9d366463a223196e9a64df','3c5e2481710c4f22d0c2babe506b0a3812c05a23fcced4939ec3d6fb1b579173','5bd49f713cc65773f9d3c6cce99bcf68248a121b65f215bd895da26c0c7767b2']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'error:' not in log and 'sorryAx' not in log;warning_count+=log.count('warning:');theorem='norm' if i<5 else 'five_norms';assert re.search(r"'DiophantineConsistency\."+n+r'\.'+theorem+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 expected=({'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'} if i<5 else dict(zip(names[:5],objects[:5])))
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==(150 if i<5 else 300)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert warning_count==17 and (a/'Sign33LiftFiveNorms-compile.txt').read_text().count('warning:')==0 and len(s['overlay_links'])==1193
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':37568,'stages':6,'reports':6,'warnings':17,'direct_guard_slots':1050,'overlay_links':1193,'scope':'five AllCuts-conditional ring norms and assembly; no Lean replay'},indent=2,sort_keys=True))
