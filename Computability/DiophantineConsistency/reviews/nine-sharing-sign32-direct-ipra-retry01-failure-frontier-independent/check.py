#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-direct-ipra-retry01';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-direct-ipra-retry01-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='1049b0cfc7b7c7235f941802d1d160ed4477c3565195ef87f727fc1d1dfb0a7c' and sha(A/'outer-result.json')=='06e7806e4d54cf82a37ac4d5678cb2903930e12207d2a268ac9b8f877a1920aa';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(1415,1) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==2 and len(s['overlay_links'])==1285 and s['runner_sha256']==sha(P/'run.py')=='495d1655c7e10c8e5c2648f033c9f0a4ffa22bf5e25b29750af922fb7aad9042' and s['base_state_sha256']=='0ea9a5c9e3b04cbf28979a4c61fc7359b768ea21e0da60bcf61b1792d64f560e'
obj='0ab66daaacfbfa8f1d32649124c8eb12ca03e5b7881ca0134041e90152532e3b';expected=[('Sign32GenericRemoveInput','b9a08e0841403425af5af4cd5fbc6c92efb6070999ca9e63d74e0077b1b03ddd',100,0,{'ModelJonesSyntax':'ca320ae03c5aece08482a0eb125d58c12d371ce524cce685428b0550a96c5171'}),('Sign32DirectExpressionSplit','d180e887c66c5487546ab4a3367396c2b1f692101089a7a02ffc4662ceaa75ba',150,-6,{'Sign32GenericRemoveInput':obj,'Sign32CurrentSourceIff':'d5dce54ef8afdd6c9a55a9c4b00816bd091995a6a34b488f8f776053e627eda1'})]
for i,(r,(n,h,c,exit,parents)) in enumerate(zip(s['rows'],expected)):
 assert r['module']==n and r['source_sha256']==h and len(r['direct_guard'])==c and sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean')==h
 if i==0:assert r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean')
 else:assert 'object_sha256' not in r and r['compile']['peak_session_rss_bytes']==2938982400
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==(0 if phase=='deps' else exit) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for mod,h in parents.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(A/'Sign32GenericRemoveInput-compile.txt').read_text();assert log.count('warning:')==2 and log.count('This simp argument is unused:')==2 and 'depends on axioms: [propext, Quot.sound]' in log and 'sorryAx' not in log
err=(A/'Sign32DirectExpressionSplit-compile.txt').read_text();assert sha(A/'Sign32DirectExpressionSplit-compile.txt')=='48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a' and 'lean::memory_exception' in err and "at 'interpreter'" in err and 'depends on axioms' not in err
R=D/'reviews/nine-sharing-sign32-direct-ipra-retry01-prelaunch-frontier-independent';assert sha(R/'check.py')=='91623257168fa46586b9d2f8809a898958d8b6d56a6b25d592bb98be9003c126' and sha(R/'result.json')=='cc58a0a0c934ffe38605f15d9e1ff83e2dc58dff345c12f69629a02849ed66b2'
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_AUDIT','author_recorded_outer_session':1415,'generic_stage':'pass, [propext, Quot.sound], two unused-simp warnings','concrete_stage':'Lean -6 interpreter memory exception, sampled peak 2938982400 bytes, monitor stop null','guard_slots':250,'overlay_links':1285,'scope':'generic evaluation theorem only; no concrete expression, endpoint or final whole-run postflight'},indent=2,sort_keys=True))
