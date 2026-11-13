#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-current-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-current-iff-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='1a9af44a56de62aad791f11141c9ae01603cd395014aa3f394ca5ba787d80db8' and sha(A/'outer-result.json')=='c762e842e61fe063549f912a074be3599df3f2eb06078e520dfd77dc077326bc'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(61275,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1079 and s['runner_sha256']==sha(P/'run.py')=='59d06591e2fef25b9fe54e4dc922fec506b71a54a2b0c5112b27927ffb6093e5' and s['base_state_sha256']=='e1722771c7075b3dd7cf30c661da8d200edc8bd1910cad3827ddf0d9c9c3284b'
r=s['rows'][0];name='Sign32CurrentSeedIff';source='539a3ee54ae3c05ac7572a1181214100c5a7cb61bf548ff1c4557871493e30f5';obj='f01ff0a7157971a45c20342da4478eff2ad82aae2aaf4e76e72c19d74a40b05c';assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==150
assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
for t in ('port0','pointwise','exists_same_input'):assert re.search(r"'DiophantineConsistency\.Sign32CurrentSeedIff\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,h in [('Sign32SeedExistential','4b265878c43d07f71055e414271c0f1c47406118aa90a088026edc9182be4f93'),('CurrentKernelData2011','95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert sha(P/'port-survey.py')=='7f64024c2f0100e9ed58a8fb2e538013bcc9414031745691b6adb615cfad50a8'
check=subprocess.run([sys.executable,'-I','-S','-B',str(P/'port-survey.py')],capture_output=True,text=True,timeout=120,check=True);assert not check.stderr and json.loads(check.stdout)['status']=='PASS'
R=D/'reviews/nine-sharing-sign32-current-iff-prelaunch-frontier-independent';assert sha(R/'check.py')=='bd3162c5093e48d87234f58c798dbb3602e5a442e6fc0c2a3ebb1b8709ab94c9' and sha(R/'result.json')=='d46470e48961d0b82405d8317f4063ad315fd2bf18fd5f72bf747b8e95a45766'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':61275,'stages':1,'guard_slots':150,'overlay_links':1079,'scope':'current-port pointwise and same-input iff; no Lean replay, JSON byte binding or sextic endpoint'},indent=2,sort_keys=True))
