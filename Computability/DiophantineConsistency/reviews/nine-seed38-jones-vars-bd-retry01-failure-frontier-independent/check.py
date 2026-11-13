#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-bd-retry01';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-vars-bd-retry01-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='24a922a65cafe434716404a587e5539965014ea5c2d6f32074f1b7c80daa6d28' and sha(A/'outer-terminal-author-record.json')=='0f382657f559541145b2f2c03b577d7c978f7a0e5f9e153ac2ecd7f48ed9a380';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(84263,1)
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1274 and s['runner_sha256']==sha(P/'run.py')=='6cc34bb110d2d37800fc7bd128e2838fdeacee72c8058ac4edcbeafb7eab8e5d' and s['base_state_sha256']=='b1709c2b60a6cd25b17ce55ead3e9aa3d5d570f15bf359e92c14c45012a046a7'
r=s['rows'][0];n='Norm38MacroVarsBd';h='013fdb21287af30502ab6d80f3690b8851ff8732215a6d5f580e6e9b941e982e';assert r['module']==n and r['source_sha256']==h and len(r['direct_guard'])==100 and 'object_sha256' not in r and sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean')==h
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==(0 if phase=='deps' else 1) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='0f9af22d72ad119b2857bef0c0299ae63121ac23fad8351962b6c3c5442539d0' and 'error: unsolved goals' in log and 'warning: This simp argument is unused' in log and 'Nat.cast_ofNat' in log and 'sorryAx' in log
v=r['dependencies']['DiophantineConsistency.Norm38MacroTerminalOutput'];assert v['sha256']=='d1362486f746e9dfeba1b94ae27f6bb770d8f15ed216fdcf2467f9a08a4bd474' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-vars-bd-retry01-prelaunch-frontier-independent';assert sha(R/'check.py')=='7394b34be3ad45b8c7f0c97c7f7f63436977001c228c860d42ef0264b8293514' and sha(R/'result.json')=='ef14edab1c3acd6669886e93742898d46ca651354854af00f9a72e02f9e38786'
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':84263,'compile_exit':1,'guard_slots':100,'overlay_links':1274,'scope':'simplification left unsolved cast-normalization goal; report contains sorryAx; no theorem or final postflight'},indent=2,sort_keys=True))
