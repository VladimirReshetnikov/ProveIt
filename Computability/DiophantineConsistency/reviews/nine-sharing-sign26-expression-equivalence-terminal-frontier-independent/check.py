#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-expression-equivalence-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-expression-equivalence-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='664707a36a938e25440bd804bc4c5e8eed9420d60f0e62236eaa6804935744de' and H(A/'outer-result.json')=='91066371b0717ed02d72c25951c4c67f1f8c19b66d3e3245313bf85c8a1298be';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(52310,0) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1084 and s['runner_sha256']==H(P/'run.py')=='f4432fd4e81231ccfeb19223930d18b4951d062bb25b5bcdf0c46cd31be0c567';r=s['rows'][0];n='Sign26ExpressionEquivalence';assert r['module']==n and r['source_sha256']=='61c4d8a616b32de63c790813b2e7f2fcd14c1b6242f2d2dd21be64dc58cccadd'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='95ab5cfb52fb67f180484780fd2f45a109b13749a3f001994f6d36f4fac0df12'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==200
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign26CurrentSeedIff','e4f6b53af38b63f08f9ca425629d7e39eef0f6c11148f93904b9bcf34cbd7ddf'),('Sign26CurrentExpressionEval','93eb07957c23cc42b56a0fd5b513495c04e8d6e8beba3da6c8e5b2c8a2232e9e'),('Sign27CurrentExpressionEval','a91b5913206a8111c9b1d6710806af7eb4985c2d7c0b63dac0fd1848e9a50d6f')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert log.count('warning:')==1 and 'automatically included section variable(s) unused' in log and 'sorryAx' not in log and 'error:' not in log
for th in ('exists_cons_iff','zero_exists_iff'):assert f"'DiophantineConsistency.Sign26ExpressionEquivalence.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-expression-equivalence-prelaunch-frontier-independent/check.py';assert H(pre)=='64f4dd34d5177b2057d5d60c06789640224c98e2e11e2dd76faafbc5a2ad17e5';
for name,h in [('nine-sharing-sign26-current-iff-terminal-frontier-independent','f71caaaa172128c46e1f30346201e225a738d84adca9e6dedbca9dc5d9d70b97'),('nine-sharing-sign26-expression-eval-terminal-frontier-independent','cfb5f67ddef456f6e82061ee17a4dd1b17d90ee2f8147207fe465085d46ef0b4'),('nine-sharing-sign27-expression-eval-terminal-frontier-independent','62e3cc909028661cfe1dcee0bd36ce5b23024f9e63e184b8e9736ec72408f00a')]:
 up=D/'reviews'/name/'check.py';assert H(up)==h;subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':52310,'guards':200,'links':1084,'scope':'sign26/sign27 direct-expression zero-existence iff over IΣ₁; no source endpoint'},sort_keys=True,indent=2))
