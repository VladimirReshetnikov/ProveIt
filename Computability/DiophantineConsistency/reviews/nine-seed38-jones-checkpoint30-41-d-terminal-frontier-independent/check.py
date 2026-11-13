#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint30-41-d-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint30-41-d-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='ddcf0459ae0bdf9ad604a7725dfed404de06f4485b434957c8c8eeeac512a7d7' and sha(a/'outer-terminal-author-record.json')=='1819a78220ed2fa6a6cdb972411d9b6cc2dba60ee12cc08812f7f9ca17ffa868';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(37462,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1245
names=['Norm38MacroDValue','Norm38MacroDPath'];objects=['eb2bacb4b0ac84fcec7cbf68943090515dcccc6f58c82e94770c4fbcdc883916','3eeb262b43d939b4af764a026281d006c0d7c05fecda77dba04fa28a9ced85db'];reports=[['d29_A_from_d27','d30_D_value'],['lookup30_34','d41_D_value']];guards=[200,150]
expected=[{'Norm38MacroAValue':'e22058fcc79740fc425fbb063007e3022a6cdc75b217385fb961a3e173dc0a31','Norm38MacroDependentD':'3fb3464ef223d9d0e7dc33fccd7d1845337aea9ccc9184c137e6664bc2026931','Norm38MacroQPath':'9b68e1bba3d3d8379632864ee79f363733d4a705b6846c08809b4e0581be55c8'},{'Norm38MacroDValue':objects[0],'Norm38MacroCheckpoint34to41':'985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointD\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 if n=='Norm38MacroDPath':assert "'DiophantineConsistency.Norm38MacroCheckpointD.path30_34' does not depend on any axioms" in log
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':37462,'stages':2,'guard_slots':350,'overlay_links':1245,'scope':'symbolic D at d41 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
