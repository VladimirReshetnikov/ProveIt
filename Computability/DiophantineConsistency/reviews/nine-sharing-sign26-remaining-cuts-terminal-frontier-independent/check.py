#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-remaining-cuts-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-remaining-cuts-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='c1f3e203f4541e33251bf599bdb4df7c9a2877678ca0927e8c2635f5910caca7' and H(A/'outer-result.json')=='37e845651b6b77315d0708f4e551e1e2b8e648cd8631bce3fbb2268cbbcdd037';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(8660,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1063 and s['runner_sha256']==H(P/'run.py')=='dbb4618c5a30639872d7b33fa0690e4ec1de59981540c790d8f41e2cfe79820d';objs=['36c6dce70ca55d327a01ba70eeb6a3f500fdea105d0056ca6b122d7b1c1bdfe8','a11be98035c1120febed4df1ed0c95b72af6801572d94ea7ede15d50d99b8f32'];groups=[[1,2,3,4,5,6,7],[10,11,13,14,15,16,17]];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,obj,inds,e) in enumerate(zip(s['rows'],objs,groups,m)):
 n=f'Sign26RemainingCuts0{i}';assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 mod,h=('Sign26CongruenceCuts','8d8280e39e611ccce749fba8b33d7a8b2a78c051b9fa83fb76e053176767e12b') if i==0 else ('Sign26RemainingCuts00',objs[0]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert log.count('warning:')==12 and log.count('linter.unusedVariables')==(10 if i==0 else 12) and log.count('linter.unusedSimpArgs')==(2 if i==0 else 0) and 'sorryAx' not in log and 'error:' not in log
 for j in inds:
  for th,ax in [(f'old_R{j:02d}_row','[propext]'),(f'new_R{j:02d}_row','[propext]'),(f'R{j:02d}_eval','[propext, Classical.choice, Quot.sound]')]:assert f"'DiophantineConsistency.Sign26RemainingCuts.{th}' depends on axioms: {ax}" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-remaining-cuts-prelaunch-frontier-independent/check.py';assert H(pre)=='3bd49efb040be6c70f7eebb36e4471cc62d583acd530a4facfe0877be2b59cee';up=D/'reviews/nine-sharing-sign26-congruence-cuts-terminal-frontier-independent/check.py';assert H(up)=='e72267a51d1d650ea77c4346360e6f0a537b78729b52b58101bf14570cf0652f';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':8660,'stages':2,'guards':200,'links':1063,'warnings':24,'scope':'14 unaffected residual identities only; no assembled zero bridge'},sort_keys=True,indent=2))
