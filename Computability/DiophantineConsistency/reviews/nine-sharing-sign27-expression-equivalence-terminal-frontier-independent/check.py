#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-expression-equivalence-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-expression-equivalence-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='2f9f2a4a7e8491aa34458e8002a37ceaf5268b94fe606cc3bf48c69a4735831a' and H(A/'outer-result.json')=='837b51e91fb668aba64e7b9ab53beb4d7f8b059ac191e489460edb8bfcd729a4';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(57475,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1094 and s['runner_sha256']==H(P/'run.py')=='41be1aefbb1d7e4ec30c0c10ae50c2bf8cd2254f208411e121f75b250cc04d1b';r=s['rows'][0];n='Sign27ExpressionEquivalence';assert r['module']==n and r['source_sha256']=='75181bd2d2ff738c1a30ac2cfa068021c9e94b80c9d225b025e34709b7bc7455'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='d50fd8e0c97401e207a88d1543725e96f951c86abf6dcd624146bb1bde9a8244'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==200
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign27CurrentExpressionEval','a91b5913206a8111c9b1d6710806af7eb4985c2d7c0b63dac0fd1848e9a50d6f'),('Sign27SeedExistential','ea89e68026255ad8866317cb855f8ded0ad88d25236e9f82f1e1d79bd9e97cd0'),('Sign28CurrentExpressionEval','2992d47b5eb75108840295f5461f5e804359bc602c7cde75908e5f2189cdc68f')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert log.count('warning:')==1 and 'linter.unusedSectionVars' in log and 'sorryAx' not in log and 'error:' not in log
for th in ['exists_cons_iff','zero_exists_iff']:assert f"'DiophantineConsistency.Sign27ExpressionEquivalence.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign27-expression-equivalence-prelaunch-frontier-independent/check.py';assert H(pre)=='f08d23b36c4001e0273529d66f127de7631fb9c578fc25cb7fdfd9bbfd0771fc'
for name,h in [('nine-sharing-sign27-seed-iff-terminal-frontier-independent','8a8ce3df5d8b9f15120ad30ab6ac188e414afb04c3a419bde36f80c13d8ffb6c'),('nine-sharing-sign27-expression-eval-terminal-frontier-independent','62e3cc909028661cfe1dcee0bd36ce5b23024f9e63e184b8e9736ec72408f00a')]:
 p=D/'reviews'/name/'check.py';assert H(p)==h;subprocess.run([sys.executable,'-I','-S','-B',str(p)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':57475,'guards':200,'links':1094,'warnings':1,'scope':'current-port sign27/28 direct-expression zero existence equivalence under IΣ₁; no source endpoint'},sort_keys=True,indent=2))
