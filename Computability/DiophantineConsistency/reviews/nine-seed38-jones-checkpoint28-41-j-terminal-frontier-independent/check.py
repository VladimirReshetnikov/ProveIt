#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint28-41-j-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint28-41-j-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='f76525e4c6c08839df9a654d494241886dbd059e86c34cbe8658f3abc234b695' and sha(a/'outer-terminal-author-record.json')=='92569fa1613768e9f100e5aa7682e396e2a61d3cfc548786a289c3c183958e95';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(50413,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1238
names=['Norm38MacroJValue','Norm38MacroJPath'];objects=['c6e4b69ed5e03ed41171bb6b85dada829f43625dc901b7de14f18305d8ac87a4','d4a2147466024442645d58e1cd9a6f0943b8ecdcf30ab6b1a5a08eb620cf3ca6'];reports=[['d28_J_value'],['lookup28_34','d41_J_value']];guards=[150,150]
expected=[{'Norm38MacroAValue':'e22058fcc79740fc425fbb063007e3022a6cdc75b217385fb961a3e173dc0a31','Norm38MacroDependentJ':'bf9afeef4f54470a90af0dea2251e33e4b66c4b7518b47fb37b089a166e09bf7'},{'Norm38MacroJValue':objects[0],'Norm38MacroCheckpoint34to41':'985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointJ\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 if n=='Norm38MacroJPath':assert "'DiophantineConsistency.Norm38MacroCheckpointJ.path28_34' does not depend on any axioms" in log
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':50413,'stages':2,'guard_slots':300,'overlay_links':1238,'scope':'symbolic J at d41 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
