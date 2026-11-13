#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint35-41-i-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint35-41-i-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='ad7e4c0e4ea16dbcd4d4d59db8c223c090fa772357298c4371e6be3bfa17cc62' and sha(a/'outer-terminal-author-record.json')=='fd634f3eb6af0b50af64b51d4d11df70734a337326ce84713a800f746fac94b1';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(84153,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1255
names=['Norm38MacroIValue','Norm38MacroIPath'];objects=['50d61e3310ff603db20ff41ce1d82d06d2bc1fd47efdc0b09fc54262b076fef1','74e27686b398042b890bbf84d9a2f1638f50b6e57502212fed6c926122212429'];reports=[['d35_I_value'],['lookup35_41','d41_I_value']];guards=[150,100]
expected=[{'Norm38MacroHPath':'d6f64fff7c7175db02b85101b9f4f112290cea47a6a80bb6ae1cee9344a20462','Norm38MacroDependentI':'c12051c12de47d4971c060cd6f4e7c1da0f0962a585f5c093861274606442d72'},{'Norm38MacroIValue':objects[0]}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointI\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 if n=='Norm38MacroIPath':assert "'DiophantineConsistency.Norm38MacroCheckpointI.path35_41' does not depend on any axioms" in log
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':84153,'stages':2,'guard_slots':250,'overlay_links':1255,'scope':'symbolic I at d41 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
