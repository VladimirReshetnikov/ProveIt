#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-seed-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-seed-iff-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='653384ed8fddb2d0e1e5f7e2a2a56ba90078ad313ffbddabf316712d3b5f7a2a' and H(A/'outer-result.json')=='60b9755c4695e06d5f2a11a5267670049bc9fbb624178988bb35dfcebfb3d8e2';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(54640,0) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1072 and s['runner_sha256']==H(P/'run.py')=='1e8b4cf4f00d580ac97e41faa8ea73ef375bfee59edfce553b4e6f65e617960f';r=s['rows'][0];n='Sign26SeedExistential';assert r['module']==n and r['source_sha256']=='b28832ff0682b3a3e0382081b51de65df650ee71eb494aad6e41bc8574a1be05'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='1578894adbad15506078a0ac7b4b71e01945985fa994efb96ddeb0659e7013a0'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
v=r['dependencies']['DiophantineConsistency.Sign26ReverseBridgeRetry'];assert v['sha256']=='5332b906ba2a44d6d44e6eed8e5557d96a8a286b6d8ed0e2afa5d3df87d3e352' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log and "'DiophantineConsistency.Sign26SeedIff.exists_same_input' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-seed-iff-prelaunch-frontier-independent/check.py';assert H(pre)=='9c0b4db64bdbd5c079e301b93355e70942bebc1f91f00deb95dc130f77cf2ae1';up=D/'reviews/nine-sharing-sign26-zero-bridge-retry02-terminal-frontier-independent/check.py';assert H(up)=='98ab4e8cc57e5f6ff4b974c2a24731d614b3a9ef1dfd2463bad690055e81e318';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':54640,'guards':100,'links':1072,'scope':'same-input sign26/sign27 zero equivalence under IΣ₁, p0/p1 casts and beta≥1; no source endpoint'},sort_keys=True,indent=2))
