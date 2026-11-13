#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint33-41-gprime-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint33-41-gprime-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='117ac3dcbaf5b172c4d99c88158daf8cc03ee9cb8a3f124832827548e1c9e31a' and sha(a/'outer-terminal-author-record.json')=='062e2df9ed47d7a68d77b4939c435777fa9c88cb116ec8803677ad16e1ae77fb';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(71385,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1251
names=['Norm38MacroGprimeValue','Norm38MacroGprimePath'];objects=['3b57637cb2e54f112ba59cf39297f71b20187df2ee31233331b0ac0a001e770a','1acfb8bf9673da2c44296cf28e642112c6018d1c25f434a420951b33352287da'];reports=[['d32_A_value','d33_Gprime_value'],['lookup33_34','d41_Gprime_value']];guards=[150,150]
expected=[{'Norm38MacroFPath':'318e2cdfe94a6e1dd389bdb01e3aad9fc32ccac34b1b0bb17e6269bdccb7c11b','Norm38MacroDependentGprime':'c2f085832ccfda5cead9ac08d342594c98ee4dcb0d24e2f40def0b92cbd784aa'},{'Norm38MacroGprimeValue':objects[0],'Norm38MacroCheckpoint34to41':'985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointGprime\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 if n=='Norm38MacroGprimePath':assert "'DiophantineConsistency.Norm38MacroCheckpointGprime.path33_34' does not depend on any axioms" in log
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':71385,'stages':2,'guard_slots':300,'overlay_links':1251,'scope':'symbolic Gprime at d41 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
