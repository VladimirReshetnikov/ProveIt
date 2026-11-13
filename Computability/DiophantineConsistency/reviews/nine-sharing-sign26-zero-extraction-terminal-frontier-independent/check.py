#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-zero-extraction-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-zero-extraction-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='ca2c2d1614fd16773f6919bcc7a758fbb444d6ea2bfd3e8fdd4d3bb980312117' and H(A/'outer-result.json')=='73528f86035ae2867531cae98375ee9fbaa8d62ec2c5917f747b69730abc774d';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(68092,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1059 and s['runner_sha256']==H(P/'run.py')=='778328a208b2af1702dd9787d6e260b75739db130941b5a1e4b28548ca25b96d';r=s['rows'][0];n='Sign26ZeroExtraction';assert r['module']==n and r['source_sha256']=='8ba3c1255b86fa2ba05925f56a5312f344d09cb72b042cd34a573d980f772784'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='d8eaa2669f1409e398da814af7a9da8560fb82e25d21cb85b0de740146331c47'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
v=r['dependencies']['DiophantineConsistency.SharingSign26Squares'];assert v['sha256']=='49bddc37c95ec053d290fc8314dc7cea089f4cce33baec24ee000fc44d573eb3' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
for th,ax in [('nt_row','[propext]'),('q3_eq','[propext, Classical.choice, Quot.sound]'),('nt_eq','[propext, Classical.choice, Quot.sound]')]:assert f"'DiophantineConsistency.Sign26ZeroExtraction.{th}' depends on axioms: {ax}" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-zero-extraction-prelaunch-frontier-independent/check.py';assert H(pre)=='a200011f77baccbb5a7b64787f3c78c9701cd097579512ef8a77d4b7ee436412';up=D/'reviews/nine-sharing-sign26-seed-squares-terminal-frontier-independent/check.py';assert H(up)=='a60bbcc769f385fd2ac4ac843ad661fa13a9668567e7f15157d3de4fa207911d';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':68092,'guards':100,'links':1059,'scope':'q3 and Nt ring equalities from sign26 seed zero with symbolic ports; no gap representative'},sort_keys=True,indent=2))
