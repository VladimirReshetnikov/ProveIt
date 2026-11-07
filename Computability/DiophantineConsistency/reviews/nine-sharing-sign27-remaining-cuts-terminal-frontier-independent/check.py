#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-remaining-cuts-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-remaining-cuts-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='89f5e3de56aebe8d58eb4842bb9274ee633031c98a0d62019a352aab4a386999' and H(A/'outer-result.json')=='5c0b341516f59870878a0cc4db96edf54bd04c132e88180ab36a8aa9e2008f68';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(18801,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1062 and s['runner_sha256']==H(P/'run.py')=='df61006a404d208289f394e29cde914e3e61e6f7ddf70074bcf1a53d74a39a33';objs=['fd1f00362e625979464197f377b9c3642f0067d3f636c4bb18614bd145fc6539','d2a7b369c4eec8c484cf88bf0aa1a1d071d1b450c1e93be3e17da8213029eb4d'];groups=[[1,2,3,4,5,9,10],[11,12,13,14,16,17,18]];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,obj,inds,e) in enumerate(zip(s['rows'],objs,groups,m)):
 n=f'Sign27RemainingCuts0{i}';assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 mod,h=('Sign27FirstCut','9451be9e6d9fb5ecdf40931b8297f66f3fd2cece8d83c36018b2b492e4b77c37') if i==0 else ('Sign27RemainingCuts00',objs[0]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert log.count('warning:')==10 and log.count('linter.unusedVariables')==(8 if i==0 else 10) and log.count('linter.unusedSimpArgs')==(2 if i==0 else 0) and 'sorryAx' not in log and 'error:' not in log
 for j in inds:
  for th,ax in [(f'old_R{j:02d}_row','[propext]'),(f'new_R{j:02d}_row','[propext]'),(f'R{j:02d}_eval','[propext, Classical.choice, Quot.sound]')]:assert f"'DiophantineConsistency.Sign27RemainingCuts.{th}' depends on axioms: {ax}" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign27-remaining-cuts-prelaunch-frontier-independent/check.py';assert H(pre)=='49cbb46db5e4df208689be92c6f23164a01c12c35577d3098640d06faad1d1e7';up=D/'reviews/nine-sharing-sign27-first-cut-retry01-terminal-frontier-independent/check.py';assert H(up)=='d049db4de12602c490af2b6649f1d6c850a5d2982014b2eddd6acc138fdb1549';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':18801,'stages':2,'guards':200,'links':1062,'warnings':20,'scope':'14 unaffected residual identities only; no assembled zero bridge'},sort_keys=True,indent=2))
