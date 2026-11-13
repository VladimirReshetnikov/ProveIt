#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint22-23-pk-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint22-23-pk-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='20e365901453dce569af438f9ed9bcf397d019888ed342dc9741ed78cad22375' and sha(a/'outer-terminal-author-record.json')=='a7f353741d712e263c710a0e9a1b11d29c1fc25147f0f8b829ddcfce33acc09f';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(89399,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1257
names=['Norm38MacroPValue','Norm38MacroKValue'];objects=['a97887bdd0fe4d62fb1cf4bc067e486e3fe1a43ec454ae3914f53b91ebd6e896','27e93856b14ee56444fd9ec4aed38eec3179043737f5e483f60824677a47c5dd'];reports=[['d22_P_value'],['d23_K_value']];guards=[150,250]
expected=[{'Norm38MacroIPath':'74e27686b398042b890bbf84d9a2f1638f50b6e57502212fed6c926122212429','Norm38MacroDependentP':'02d7d218dd922bd33bf7e8f6aad2533855fe157dbd3ea844b5111a335c9db964'},{'Norm38MacroPValue':objects[0],'Norm38MacroDependentK':'54542c0eb712eb19b70ae07aef9308156edf7fc4311e177d00fb8181278a5f9d','Norm38MacroLive18Group02':'f028ef640af09a6477b7672e76630057147c859c26d908dafded919953f8a53c','Norm38MacroPrefixInputsA':'ab8025bff041d6816025d2457dc12f9d5fa4e6072d399a8b8767d16bcbb2faf9'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointPK\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':89399,'stages':2,'guard_slots':400,'overlay_links':1257,'scope':'symbolic P/K local nodes with opaque rank; no Lean replay'},indent=2,sort_keys=True))
