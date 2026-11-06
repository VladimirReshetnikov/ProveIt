#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint21-27-m-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint21-27-m-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='cb6fa1cd0b7095593dc220e13defcaf581274de317cc2f1ff2b0bc5ff821cc8b' and sha(a/'outer-terminal-author-record.json')=='145d15fab29d150e4dee2c8808b5c66610aab2dac519bc6c22a83b0c8140e314';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(67708,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1234
names=['Norm38MacroMPath','Norm38MacroMValue'];objects=['5e7634306ffcef9bd3b5f6ee4d6d5ed70e2c4b9157b2ae9fa45638a08f940e6c','aa0ba07d953598aa407e4d3c6356cc73bddd1d8b104b48440a24aad8db34695f'];reports=[['lookup21_27'],['d27_M_value']];guards=[100,200]
expected=[{'Norm38MacroUYValues':'5be1513afe23c53b5207db78352da17597e1d45c6c8441aaa26695c4f7e9d092'},{'Norm38MacroMPath':objects[0],'Norm38MacroDependentM':'81363f56b3ea598151f89eda0e9cce2bdeca9c7b2a989b20739059343eb72454','Norm38MacroLive18Group02':'f028ef640af09a6477b7672e76630057147c859c26d908dafded919953f8a53c'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointM\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 if n=='Norm38MacroMPath':assert "'DiophantineConsistency.Norm38MacroCheckpointM.path21_27' does not depend on any axioms" in log
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':67708,'stages':2,'guard_slots':300,'overlay_links':1234,'scope':'symbolic M at d27 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
