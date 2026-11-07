#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-compact-language-import-retry01';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-compact-language-import-retry01-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='bc4a7082cabf867f1b4db1560f3f76066d184ca7bc34588d430ea83f867ae2fc' and sha(A/'outer-terminal-author-record.json')=='bd742fcb3814ebfc08db0c70669c2ea1f57d5869ef7128e956bd73f462d98883';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(46571,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1056 and s['runner_sha256']==sha(P/'run.py')=='eb214ef13ee2ab5c8c61d339afa2cb0383b636bdecfa91a2a6cd7ce82e2d8b20';r=s['rows'][0];n='Sign33MacroLanguage';assert r['module']==n and r['source_sha256']=='7bea6cf1ea90c54007de2eab62afad11d06328bfd27df3ffea0afbe34bd16fa1'==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='9e1b3c12f306411cfc650eaf0182042ae607a81b4b75f8cc660f0daf46bea4d3'==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
for mod,h in {'SharingSeed33Syntax':'d8d70064be0d7fa609b92a8b51648b6e817096886e0671f37d64271f05e21be0','CurrentKernelData2011':'95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896'}.items():
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (A/f'{n}-compile.txt').read_bytes()==b''
review=D/'reviews/nine-seed33-jones-compact-language-import-retry01-prelaunch-frontier-independent/check.py';assert sha(review)=='2430c61b7ce06aecef292a2378c6d49f4d0a79d628bdc958ba7359b7dcd41c4b';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':46571,'guard_slots':150,'overlay_links':1056,'scope':'sign33 language definitions only; no axiom report requested and no recipe or semantic equality'},indent=2,sort_keys=True))
