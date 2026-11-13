#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-first-cut-retry01';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-first-cut-retry01-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='b64c131ca441633bd6528d126cf9f9fa3d3e972c602096e253619406f5fa21a7' and H(A/'outer-result.json')=='b814f85b2bddb781701666c669d4feef3203041fab0b6693cef3d564d209b953'
s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1061 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(21863,0) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='b75ec37d48d49cff2bc920a28bc8ce4761eb4e113344d88af1dc9947cdf5b930'
r=s['rows'][0];n='Sign27FirstCut';assert r['module']==n and r['source_sha256']=='edf59a6e7590fa6f7940f86c597ff1eb21f5acb3337fb89a0c6b5aa2add296a1'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==150
for phase,exit in [('deps',0),('compile',0)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
log=(A/f'{n}-compile.txt').read_text();assert log.count('warning:')==2 and 'unusedSimpArgs' in log and 'unnecessarySeqFocus' in log and 'sorryAx' not in log and 'error:' not in log
for th,axioms in [('oldN1_row','[propext]'),('oldN1_zero','[propext, Classical.choice, Quot.sound]'),('first_eval','[propext, Classical.choice, Quot.sound]')]:assert f"'DiophantineConsistency.Sign27FirstCut.{th}' depends on axioms: {axioms}" in ' '.join(log.split())
assert r['object_sha256']=='9451be9e6d9fb5ecdf40931b8297f66f3fd2cece8d83c36018b2b492e4b77c37'==H(O/'lib/DiophantineConsistency'/f'{n}.olean')
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('SharingSign27Squares','b7f2a083a1a7a81d57b6fafe67670d8065f43f57396cc2503a38bda0f078bd40'),('SharingSign28Squares','942397e7cb222881da765f30804b2c4775673cba5a324cb58f0c51416d6c3f04')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign27-first-cut-retry01-prelaunch-frontier-independent/check.py';assert H(review)=='9cd56d77e298955e90c068fbfdb3cbdba07d4d4227a664594bbb40a4da08054d'
survey=P/'sign28-survey.py';assert H(survey)=='eda25e29ad5397a980627ebfc04687b5b2b07a0adb7ce5ef3788b5e4ae0bfeff';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':21863,'outer_exit':0,'lean_exit':0,'guards':150,'links':1061,'scope':'first cut only; two proof linter warnings; no full zero bridge'},sort_keys=True,indent=2))
