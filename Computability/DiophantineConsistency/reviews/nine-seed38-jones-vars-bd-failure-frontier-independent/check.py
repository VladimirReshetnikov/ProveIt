#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-bd-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-vars-bd-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='d02ac5f064202ad397b2951e0a99b5945493ee20f3e68d196dbefb126fe9b946' and sha(A/'outer-terminal-author-record.json')=='f34bb160acf8b66ab9182392b677d0628374e5efeca7e5b2d4e285c08ca18c40';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(97794,1)
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1274 and s['runner_sha256']==sha(P/'run.py')=='83fe59cc59138c306b1c570821e1b860b9df17874426b531e6b120bc8ddaf4b0' and s['base_state_sha256']=='b1709c2b60a6cd25b17ce55ead3e9aa3d5d570f15bf359e92c14c45012a046a7'
r=s['rows'][0];n='Norm38MacroVarsBd';h='3b3e3dbfef6652d6de7b20fdf55007e9d7976f1bfc287e593b21aecd252d590c';assert r['module']==n and r['source_sha256']==h and len(r['direct_guard'])==100 and 'object_sha256' not in r and sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean')==h
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==(0 if phase=='deps' else 1) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='1dc1bc0ee942c8af4ec5f0a68a49ae95d8cf19ec97caf141b80418790e84e455' and 'error: Tactic `rfl` failed' in log and '(vars a).dvsr' in log and 'sorryAx' in log
v=r['dependencies']['DiophantineConsistency.Norm38MacroTerminalOutput'];assert v['sha256']=='d1362486f746e9dfeba1b94ae27f6bb770d8f15ed216fdcf2467f9a08a4bd474' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-vars-bd-prelaunch-frontier-independent';assert sha(R/'check.py')=='3c406f4c3f7cffebedf2f37c64a391a49889e811ad3d233b16b5f4b2f04dffd7' and sha(R/'result.json')=='ed74d55f2426af17434cfc95c71fe13d3d9dda06f0c9ab4e4e3f8e9778c2c89f'
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':97794,'compile_exit':1,'guard_slots':100,'overlay_links':1274,'scope':'final rfl did not close Bd versus vars.dvsr; report contains sorryAx; no theorem or final postflight'},indent=2,sort_keys=True))
