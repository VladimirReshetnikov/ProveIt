#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-seed-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-seed-iff-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='e1722771c7075b3dd7cf30c661da8d200edc8bd1910cad3827ddf0d9c9c3284b' and sha(A/'outer-result.json')=='338761611994563d27d9366772a51dcab8a685df62fd1d377c2bdf3980c89094'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(39485,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1077 and s['runner_sha256']==sha(P/'run.py')=='6604e5f7eda0818a32875730cf163b81c009f61f4bed4a7bcd4fa004272e02f5'
objs=['0794c01e297d4722a7ea81d6f34096733f75d5a9af62eb1b82bd4c924e16a493','4b265878c43d07f71055e414271c0f1c47406118aa90a088026edc9182be4f93']
expect=[('Sign32SeedPointwise','6d5c1226c890f268d8b3aa9530bd6f6e01b1920d35a5492723d296ae6f8b9a88',150,{'Sign32ForwardAssemblyAll':'a31790adc97b9b51b6b5c9e2f3246540e82ff87f4137637569f25849120f7686','Sign32ReverseAssemblyAll':'eb9f10c3511e763140f514d6ee298fc456601499652dbe85dcb5df70c69f1bb3'}),('Sign32SeedExistential','2a95bc5012676916c31b0aafeb919cc565f475896b131ef5c259957bf089028c',100,{'Sign32SeedPointwise':objs[0]})]
for row,obj,(name,source,count,producers) in zip(s['rows'],objs,expect):
 assert row['module']==name and row['source_sha256']==source and row['object_sha256']==obj and len(row['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=row[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 reports=['drop_lift','pointwise'] if name=='Sign32SeedPointwise' else ['exists_same_input']
 for theorem in reports:assert re.search(r"'DiophantineConsistency\.Sign32SeedIff\."+theorem+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for mod,h in producers.items():
  v=row['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and row['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in row['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert sha(P/'survey.py')=='a66a919b77028966abb5912e8aadb57a6824fd1707f3ea55e9bc9a6e937939e0'
check=subprocess.run([sys.executable,'-I','-S','-B',str(P/'survey.py')],capture_output=True,text=True,timeout=120,check=True);assert not check.stderr and json.loads(check.stdout)['status']=='PASS' and json.loads(check.stdout)['producer_rows']==12
R=D/'reviews/nine-sharing-sign32-seed-iff-prelaunch-frontier-independent';assert sha(R/'check.py')=='d8f99faa6d351d17bb815d74b2c7bcff75cc31470e9f9f7b01ecac464b38cade' and sha(R/'result.json')=='4c32c7324209e9e05da00d440701c5d5eec8fe5504c5475d20f19508711a4be9'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':39485,'stages':2,'guard_slots':250,'overlay_links':1077,'scope':'symbolic pointwise and same-input existential 32↔33 seed iff under hp0; no Lean replay, current ports or endpoint'},indent=2,sort_keys=True))
