#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint20-27-uy-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint20-27-uy-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='1c2fdd4941facbef11ff87136ac33af55c5fe872689b645fbf15d09e7cf01bf0' and sha(a/'outer-terminal-author-record.json')=='971e327e93bc0daca236cff13e339ea3d4a06e4e31fb9a5efbdb81d4eb4f3fac';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(4085,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1231
names=['Norm38MacroUYInputs','Norm38MacroUYPath','Norm38MacroUYValues'];objects=['26bf3e4788614e5d5efe6d131734539f551d9d8cbc50fb65b8b017d3b2ff828e','6c8dae428b5c6c451da10b83e9ccd14038cd42d375d7b6232e1d3c6cff97c900','5be1513afe23c53b5207db78352da17597e1d45c6c8441aaa26695c4f7e9d092'];reports=[['d18_N_value','d18_s_value','d18_w_value'],['lookup20_27'],['d27_U_value','d27_Y_value']];guards=[300,100,150]
expected=[{'Norm38MacroCheckpoint41to45':'d0dc8713317ad6f6b829c3776d740169273d9abecbf5a344489c148fb04cb565','Norm38MacroLive18Group01':'b2c531a9eecdd13baaf18f2f130949cd8fd7602118f575cd124fffa4b0dc32dd','Norm38MacroLive18Group03':'2589ac6c78d736a31bd3e851aaa0068d43ec0a10a10b3cb648b4df8b7da9d902','Norm38MacroPrefixInputsA':'ab8025bff041d6816025d2457dc12f9d5fa4e6072d399a8b8767d16bcbb2faf9','Norm38MacroPrefixQNCarry':'bd2995f482e56f212b821cb5ced4a9f660119720e20a57cb71aeedf9294c194c'},{'Norm38MacroUYInputs':objects[0]},{'Norm38MacroUYPath':objects[1],'Norm38MacroDependentY':'eb28e13077c175963702682ff8501cb25c4036813d5d035c3574a9e605f516a9'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointUY\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 if n=='Norm38MacroUYPath':assert "'DiophantineConsistency.Norm38MacroCheckpointUY.path20_27' does not depend on any axioms" in log
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':4085,'stages':3,'guard_slots':550,'overlay_links':1231,'scope':'symbolic U/Y at d27 and local path; no Lean replay'},indent=2,sort_keys=True))
