#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-seed-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign25-seed-iff-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='b33666339eec6405949f1835ebaaf6e034dbab392bb5e7d337c5f3c42c4c52b6' and H(A/'outer-result.json')=='d1b09def169083be7e6b1581d760e0e2829ef169db515dc7ea48602d6c981b15';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(5404,0) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1068 and s['runner_sha256']==H(P/'run.py')=='64da796c356227c630158c688c2a739b3e42a47d734655a7561e4c00fcda24d4';r=s['rows'][0];n='Sign25SeedExistential';assert r['module']==n and r['source_sha256']=='60edcbb246cf89ad2719492c71ceed7b2f1c681cd7b14f05b15cec1c450d47c7'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='ffc2393e2eae606147b1de0eb24c1a6c38c28fbadff569644ee5e80d23736c2d'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
v=r['dependencies']['DiophantineConsistency.Sign25ReverseBridge'];assert v['sha256']=='2b7b552bfa3143958677bba12bea17e571061382058209c686bb42d60e71c9ab' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log and "'DiophantineConsistency.Sign25SeedIff.exists_same_input' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign25-seed-iff-prelaunch-frontier-independent/check.py';assert H(pre)=='ce41ce7e87e1d388ae042a57ab8f3b0809b1630b2e135be6fa1a30afb99273d7';up=D/'reviews/nine-sharing-sign25-zero-assembly-terminal-frontier-independent/check.py';assert H(up)=='617b1d0fb214ceb49bd75695f3b99b01b01a6aeb57b9f9165c22e9c8634d8cc7';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':5404,'guards':100,'links':1068,'scope':'same-input sign25/sign26 zero equivalence under IΣ₁ for symbolic ports; no endpoint'},sort_keys=True,indent=2))
