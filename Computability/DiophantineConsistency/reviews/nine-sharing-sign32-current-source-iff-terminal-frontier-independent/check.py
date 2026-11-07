#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-current-source-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-current-source-iff-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='0ea9a5c9e3b04cbf28979a4c61fc7359b768ea21e0da60bcf61b1792d64f560e' and sha(A/'outer-result.json')=='81e6c45cf4a536c26d4fccb29aaef8f8a90f4b477325ef816d4f0fe25f3086e0'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(53754,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1284 and s['runner_sha256']==sha(P/'run.py')=='5967dfd049431626a954f0b726e4b6a143116f3ba468856a99a4fe5d7b7fead7' and s['base_state_sha256']=='1a9af44a56de62aad791f11141c9ae01603cd395014aa3f394ca5ba787d80db8'
r=s['rows'][0];name='Sign32CurrentSourceIff';source='94ae8b464dd8ed029f20fa4561a1a911c688419c6618f749194d930c9fd9f5bb';obj='d5dce54ef8afdd6c9a55a9c4b00816bd091995a6a34b488f8f776053e627eda1';assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==150
assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'error:|sorryAx',log) and log.count('warning:')==1 and 'automatically included section variable(s) unused' in log
for t in ('exists_cons_iff','seed_exists_iff_source'):assert re.search(r"'DiophantineConsistency\.Sign32CurrentSourceIff\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,h in [('Sign32CurrentSeedIff','f01ff0a7157971a45c20342da4478eff2ad82aae2aaf4e76e72c19d74a40b05c'),('Sign33CurrentSeedIff','e4e6780fd199443f88f1b142f8eb284757c1293e3b0aa804c3d0f4d3af963670')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert sha(P/'union-survey.py')=='5b7fcc23a8ab41e3bba35df2cc5b3d560fddb4bb4b97fc633d755d618e4736b0'
check=subprocess.run([sys.executable,'-I','-S','-B',str(P/'union-survey.py')],capture_output=True,text=True,timeout=120,check=True);assert not check.stderr and json.loads(check.stdout)['status']=='PASS' and json.loads(check.stdout)['overlap']==1057 and json.loads(check.stdout)['injected_extra']==203
R=D/'reviews/nine-sharing-sign32-current-source-iff-prelaunch-frontier-independent';assert sha(R/'check.py')=='73721aaa19554902fedff0982f6cde10f1ad5abd67bb76beb36eb6c02bd41e8a' and sha(R/'result.json')=='c58f23f429ecbff37a1bb97141ddac7da8cf8da52647443a865fe78a3d9b6749'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':53754,'stages':1,'guard_slots':150,'overlay_links':1284,'scope':'current sextic 32-witness input1 iff 14-variable source; no Lean replay, JSON byte binding or sextic endpoint'},indent=2,sort_keys=True))
