#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-first-cut-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-first-cut-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='0d3d8fd1f314a2eb6153c3bc166d6dd434d40b4098717b19a95e579cb20a601e' and H(A/'outer-result.json')=='bb9e4d910aa2450b38af114bba531f05bf6bb4bf0254f07c6ff4f7cd2373306f'
s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1061 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(24677,1) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='8868b9de3d9791eb0ebc4b4306b6faf7b27688f2cb885aa5c6effd0529caf945'
r=s['rows'][0];n='Sign27FirstCut';assert r['module']==n and r['source_sha256']=='6219d8aa463618455ada24b85a10ee269cee1593ca3668872768581182f63719'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==150
for phase,exit in [('deps',0),('compile',1)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
log=(A/f'{n}-compile.txt').read_text();assert 'ι (v 21) * 2 - ι (v 21) * ι 2 = 0' in log and log.count('warning:')==1 and 'unusedSimpArgs' in log and 'sorryAx' in log
assert 'object_sha256' not in r and not (O/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('SharingSign27Squares','b7f2a083a1a7a81d57b6fafe67670d8065f43f57396cc2503a38bda0f078bd40'),('SharingSign28Squares','942397e7cb222881da765f30804b2c4775673cba5a324cb58f0c51416d6c3f04')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign27-first-cut-prelaunch-frontier-independent/check.py';assert H(review)=='d5ebfc7b645324d9c865771695f856befdc071b1d6b137fe4348f65ef5d1c317'
survey=P/'sign28-survey.py';assert H(survey)=='eda25e29ad5397a980627ebfc04687b5b2b07a0adb7ce5ef3788b5e4ae0bfeff';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':24677,'outer_exit':1,'lean_exit':1,'guards':150,'links':1061,'scope':'error-contaminated report; no successful theorem or whole-run final postflight'},sort_keys=True,indent=2))
