#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint36-41-a0-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint36-41-a0-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='3223b4ced8c30d3f1de22fdd621720d0081fea7ee6ff05ee45921c8bd0ca9404' and sha(a/'outer-terminal-author-record.json')=='253610e6bf6f52cac670d5a50cd946498d2858d46787242c9b4c3083a2a9ceff';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(69751,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1259
names=['Norm38MacroPKPaths','Norm38MacroA0Value','Norm38MacroA0Path'];objs=['15bac190a41fa15b95e579d87431eb857f02e37d5ca1df340a83484dc02421ec','9c6fc49057adbac5d4484f8c8955fb7f8c1bfe02c32d6a5e2c2fe51ee6a4969a','d8915cf6fe8fc9245466662f0d3c6389a0d4141d36af507fa8797d580ff5c043'];reports=[(['lookup22_27','lookup23_27'],['path22_27','path23_27']),(['d35_P_value','d35_K_value','d36_A0_value'],[]),(['lookup36_41','d41_A0_value'],['path36_41'])];guards=[100,150,100]
expected=[{'Norm38MacroKValue':'27e93856b14ee56444fd9ec4aed38eec3179043737f5e483f60824677a47c5dd'},{'Norm38MacroPKPaths':objs[0],'Norm38MacroDependentA0':'eff7a82240baac63d26df27eb612b3c1104971b0540666aa076855cd8890a9d4'},{'Norm38MacroA0Value':objs[1]}]
for r,n,h,(std,pure),gn,ex in zip(s['rows'],names,objs,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in std:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointA0\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure:assert f"'DiophantineConsistency.Norm38MacroCheckpointA0.{t}' does not depend on any axioms" in log
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=900);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':69751,'stages':3,'guard_slots':350,'overlay_links':1259,'scope':'symbolic A0 at d41 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
