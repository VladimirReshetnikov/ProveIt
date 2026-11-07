#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-direct-ipra-abstract-split';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-direct-ipra-abstract-split-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='e2712b4fdf278aa23707edb92b43af8b24e0f8f58182c2135a7d93f0b9d9d2f6' and sha(A/'outer-result.json')=='45b74f446628fd587a52ddf64d7bdbb14fe78344d08bcda2fc3b4eaec57184bf';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(89873,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1286 and s['runner_sha256']==sha(P/'run.py')=='5a98db2ab91ce75fc2afdcc638652e750989cb638041718a5b1d113a99906cac'
names=['Sign32AbstractExpressionDef','Sign32AbstractExpressionEval','Sign32CurrentExpressionDef','Sign32CurrentExpressionEval'];objects=['31128c84c8f3d42827112be70142c23b2631dbb860906b31c59e37f70412924f','e4fa9a222d6688cfc9a7602ac4dcbc5964ca830444c18cc4f6518b50139680c9','b4e6230b70812f836090fc27cbb9365aa061847dfc4dcfb532156769432032de','558f9c63e6eda87224cca52d8dc22a2f0c3d6ba5ba9b22a8e3321f7f6b5fa109'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==(150 if i==0 else 100)
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 expected={'Sign32GenericRemoveInput':'0ab66daaacfbfa8f1d32649124c8eb12ca03e5b7881ca0134041e90152532e3b','Sign32CurrentSourceIff':'d5dce54ef8afdd6c9a55a9c4b00816bd091995a6a34b488f8f776053e627eda1'} if i==0 else {names[i-1]:objects[i-1]}
 for mod,h in expected.items():
  rec=r['dependencies']['DiophantineConsistency.'+mod];assert rec['sha256']==h and r['direct_guard'][rec['path']]=={'sha256':h,'realpath':rec['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 if i in (1,3):assert 'depends on axioms: [propext, Classical.choice, Quot.sound]' in ' '.join(log.split())
 else:assert log==''
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign32-direct-ipra-abstract-split-prelaunch-frontier-independent/check.py';assert sha(review)=='892caec42f0442dac9a2cf3fd5cd835c53d86cb7ff90f71c82595d6f10171583';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':89873,'stages':4,'guard_slots':450,'overlay_links':1286,'scope':'abstract and fixed-port expression evaluation only; no endpoint, Lean degree, or JSON binding; author-recorded outer exit'},indent=2,sort_keys=True))
