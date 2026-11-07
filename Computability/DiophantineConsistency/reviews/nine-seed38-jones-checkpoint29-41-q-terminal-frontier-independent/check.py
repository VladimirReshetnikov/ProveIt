#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint29-41-q-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint29-41-q-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='3044c9fac066bb5f73221ba4a0948266eafa36b4a9ad2fbc70833f93223ff93e' and sha(a/'outer-terminal-author-record.json')=='a2005e7dc3b6f25de18506685e4acbb11852a6863f0fc9221be836be142953f1';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(90739,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1243
names=['Norm38MacroQValue','Norm38MacroQPath'];objects=['3dd2aee6098a3ddd5ede43c5d135c6169760a1d7eeb37159e04f8c27ab241658','9b68e1bba3d3d8379632864ee79f363733d4a705b6846c08809b4e0581be55c8'];reports=[['d29_Q_value'],['lookup29_34','d41_Q_value']];guards=[150,150]
expected=[{'Norm38MacroCValue':'460ceb6124d38eedff80b049022612adcd2e4f8a5fbd76dd6e44fcfa532ea764','Norm38MacroDependentQ':'a306bbaa1f89b688b9a99bcd7146fa0b989eb1c0574810c6197c7a518b461840'},{'Norm38MacroQValue':objects[0],'Norm38MacroCheckpoint34to41':'985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointQ\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 if n=='Norm38MacroQPath':assert "'DiophantineConsistency.Norm38MacroCheckpointQ.path29_34' does not depend on any axioms" in log
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':90739,'stages':2,'guard_slots':300,'overlay_links':1243,'scope':'symbolic Q at d41 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
