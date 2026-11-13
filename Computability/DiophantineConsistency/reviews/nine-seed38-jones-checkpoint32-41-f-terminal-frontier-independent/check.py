#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint32-41-f-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint32-41-f-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='803ef893e7ae7022dfe6aa160b6e9293fc4cf87e6dcc5a16bad5c5d7ae7c07f5' and sha(a/'outer-terminal-author-record.json')=='278f1f03ea0a5da28ec1c203797df620c5a3dfc744cb31348795dbed4975cfc5';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(79419,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1249
names=['Norm38MacroFValue','Norm38MacroFPath'];objects=['e00365a17c9c269b41a4ee9c6a2a5f69894c99959a8d310cdbe4775889de9803','318e2cdfe94a6e1dd389bdb01e3aad9fc32ccac34b1b0bb17e6269bdccb7c11b'];reports=[['d31_A_from_d29','d32_F_value'],['lookup32_34','d41_F_value']];guards=[150,150]
expected=[{'Norm38MacroEPath':'87b518d9d42c7ba288eed4b25cc6060a96a47236bfc7441de75240bc1737bb89','Norm38MacroDependentF':'a7700d99911c457d906075eccae9433ac825b8b9fc0df269c01bfd66426b2118'},{'Norm38MacroFValue':objects[0],'Norm38MacroCheckpoint34to41':'985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointF\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 if n=='Norm38MacroFPath':assert "'DiophantineConsistency.Norm38MacroCheckpointF.path32_34' does not depend on any axioms" in log
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':79419,'stages':2,'guard_slots':300,'overlay_links':1249,'scope':'symbolic F at d41 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
