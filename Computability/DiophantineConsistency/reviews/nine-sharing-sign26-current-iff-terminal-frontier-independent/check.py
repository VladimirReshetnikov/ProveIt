#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-current-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-current-iff-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='2668d50f27d9d2b7efe0605e2e0d31bf7fdfd097baf4f1118581eadd096a7c4f' and H(A/'outer-result.json')=='805cbae54e4b906eefcf99a0f2073f3d3bb3ee68db989cf2fbabeb86ba674997';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(36759,0) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1074 and s['runner_sha256']==H(P/'run.py')=='527e1e80355e02e56c6a29cb5d3951223632d8c836125f8a8f1ecaa6fc52d615';r=s['rows'][0];n='Sign26CurrentSeedIff';assert r['module']==n and r['source_sha256']=='a8e8b842f1b209411166560e73a3be695a8821e7d3a8037dc1a282cb5e7ca482'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='e4f6b53af38b63f08f9ca425629d7e39eef0f6c11148f93904b9bcf34cbd7ddf'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign26SeedExistential','1578894adbad15506078a0ac7b4b71e01945985fa994efb96ddeb0659e7013a0'),('Sign26CurrentHypotheses','c4692189c4b27b48777b545bfa7829f01a06916d3d7c43a4de09602752efb88c')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log and "'DiophantineConsistency.Sign26CurrentSeedIff.exists_same_input' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-current-iff-prelaunch-frontier-independent/check.py';assert H(pre)=='b42bcfd61278ccfdbbdc1d806070b0d3c72b194f6b7843b8a04ada3d11ce1333';
for name,h in [('nine-sharing-sign26-seed-iff-terminal-frontier-independent','b78b92433be6cbc79eab65ffe3639b6c638289cec21aa40c86ca13bdd924e7f5'),('nine-sharing-sign26-current-hypotheses-terminal-frontier-independent','4f4eb9907e1139cc3fc03f358d0972667f32735fa687bbe8ae8e44eebae115bc')]:
 up=D/'reviews'/name/'check.py';assert H(up)==h;subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':36759,'guards':150,'links':1074,'scope':'current-port same-input sign26/sign27 seed iff in IΣ₁; no source endpoint'},sort_keys=True,indent=2))
