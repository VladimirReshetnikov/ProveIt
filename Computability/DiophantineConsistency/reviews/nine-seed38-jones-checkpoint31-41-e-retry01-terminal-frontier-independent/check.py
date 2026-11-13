#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint31-41-e-retry01';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint31-41-e-retry01-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='fbff308a86c3ca4af137a0ec1bff80610920fe465c71961e5c59c9f31bbffe47' and sha(a/'outer-terminal-author-record.json')=='bff774ccef390d5d730730bffabb0181315213abbb17cd7e4aaf0008d6ef542e';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(60236,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1247
names=['Norm38MacroEValue','Norm38MacroEPath'];objects=['532b55ead0f186b9b8687f22652d893e9acef668c5d900f1a4de8dc687334b87','87b518d9d42c7ba288eed4b25cc6060a96a47236bfc7441de75240bc1737bb89'];reports=[['d30_i_value','d31_E_value'],['lookup31_34','d41_E_value']];guards=[300,150]
expected=[{'Norm38MacroDPath':'3eeb262b43d939b4af764a026281d006c0d7c05fecda77dba04fa28a9ced85db','Norm38MacroDependentE':'bc5eda5787bcabd4e9ae026819ab20bb299dfdd4aff76d59f7e3e3dc9fb85433','Norm38MacroJValue':'c6e4b69ed5e03ed41171bb6b85dada829f43625dc901b7de14f18305d8ac87a4','Norm38MacroLive18Group04':'d441a380efaacb979a20ed3370cfec35c900afd19d23eaa210b1b7d6bb76c143','Norm38MacroPrefixInputsB':'43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170'},{'Norm38MacroEValue':objects[0],'Norm38MacroCheckpoint34to41':'985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointE\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 if n=='Norm38MacroEPath':assert "'DiophantineConsistency.Norm38MacroCheckpointE.path31_34' does not depend on any axioms" in log
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':60236,'stages':2,'guard_slots':450,'overlay_links':1247,'scope':'symbolic E at d41 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
