#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-current-seed-gap-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-current-seed-gap-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='1b4d5fe331ecb0ba34af2f87436dc30a87ed8c4b93392786c62838e8fe096d82' and H(A/'outer-result.json')=='2439b4daba2cea0d03e3885a4002a357bd115ce41ee1bfef0ac05817342ee947';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(91619,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1064 and s['runner_sha256']==H(P/'run.py')=='912121dafc442885673dabceb2997d2225c7064bf0537d8cd4ba03f567c1a243';r=s['rows'][0];n='Sign26CurrentSeedGap';assert r['module']==n and r['source_sha256']=='5ce4dc1f7c68393e7c4faa6156294c8809568bc82a1bc5c13da98cc37ddd2545'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='f4e1751714b8ae35d785f384f796ca2be5dd57cacd50ca61f5e623150e591078'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
v=r['dependencies']['DiophantineConsistency.Sign26CurrentHypotheses'];assert v['sha256']=='c4692189c4b27b48777b545bfa7829f01a06916d3d7c43a4de09602752efb88c' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log and "'DiophantineConsistency.Sign26CurrentSeedGap.exists_gap' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-current-seed-gap-prelaunch-frontier-independent/check.py';assert H(pre)=='706e4fb0437b6ff0b837b5787649d0a70508239b609306d077d888d20b8f1e3d';up=D/'reviews/nine-sharing-sign26-current-hypotheses-terminal-frontier-independent/check.py';assert H(up)=='4f4eb9907e1139cc3fc03f358d0972667f32735fa687bbe8ae8e44eebae115bc';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':91619,'guards':100,'links':1064,'scope':'current-port sign26 seed zero yields represented gap under IΣ₁; no residual bridge'},sort_keys=True,indent=2))
