#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-path18-45-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-prefix-path18-45-staged-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='aa759798f6726970f460be1bd46bb99d5c361d428a7cf386b7743671e7c82cdb' and H(A/'outer-terminal-author-record.json')=='fdfe6d45e5ca23b3dd88f5e8509c03f4713649b6dba5625aaf626849a0a40cbf';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(51134,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==5 and len(s['overlay_links'])==1114 and s['runner_sha256']==H(P/'run.py')=='873ae4af6a0db433fba0c3f7ba403b9942881e47f615c72e7c29a171b6b394ba'
ends=[20,27,34,41,45];objects=['24b167d4cc5a25e9ca84b7a750ccce19b84d34dc45cd470277574e24e5c7fee0','d45f3e9734ec3678e629089117df51852e33e528732e7d460dac10c0c9dda69a','ac005141d5a1a99025d567b8caaaf793e780bed9cd02f704107dfd16d24c4ea2','d52d1483ef0134399692074405affe0dc2efecaabe4770e7e9bbd2800bb3ddcb','4c4ef02f8f9c200b7c20313cc08edd9bd359e3056aa5c00b79b02ee1a335f1a2'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(end,r,obj,e) in enumerate(zip(ends,s['rows'],objects,m)):
 n=f'Sign33MacroPath18to{end}';assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==(150 if i==0 else 100)
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 deps=[('Sign33MacroDependentOutput','36c16fb1daf0dcde1169dfb9468f2657f4d6e48fcae7c29c4155b84c6a65ffe3'),('Sign33MacroPrefixEmbedding','8bf6d79a1c5313487c4b74d683480d49f73d2485f81b442c41f442223137b305')] if i==0 else [(f'Sign33MacroPath18to{ends[i-1]}',objects[i-1])]
 for mod,h in deps:
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 assert f"'DiophantineConsistency.{n}.path18_{end}' does not depend on any axioms" in log
 for th in [f'lookup18_{end}']+(['lookup_recipe18'] if end==45 else []):assert f"'DiophantineConsistency.{n}.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-prefix-path18-45-staged-prelaunch-frontier-independent/check.py';assert H(pre)=='0656a31d4d8057ff7b6c00582d7dfdbc48ade95d28db68a66b14ff3b528f96c5'
up=D/'reviews/nine-seed33-jones-dependent08-staged-terminal-frontier-independent/check.py';assert H(up)=='f8908d411729a7b1f1bcf121aeb653e43f7902749bf83a8dca7e40e03291f0ce';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':51134,'stages':5,'guard_slots':550,'links':1114,'scope':'Fin18 checkpoint and recipe lookups only; no composed output semantics'},sort_keys=True,indent=2))
