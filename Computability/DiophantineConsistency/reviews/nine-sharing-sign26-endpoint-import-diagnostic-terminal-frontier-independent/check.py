#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-endpoint-import-diagnostic';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-endpoint-import-diagnostic-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='4eb39bdc7472db2f455262be311ff3f448b50842c293d0e01f4b1997dba15884' and H(A/'outer-result.json')=='16b04fed8855a274eaeb7de5854b3f6f8c122108aef3b7f8148dbe6e1dfd9ca0';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'],o['state_sha256'])==(50716,0,H(A/'state.json'))
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1366 and s['runner_sha256']==H(P/'run.py')=='9f6efabbfa3977b7f953c9fcfb1157241e6227145eaeebc9cf5f318da6110305'
names=['Sign26ImportFramework','Sign26ImportBridge','Sign26ImportBoth'];objs=['51555e4a3a5cf0e4b4752f931835c5037f8fc55c7a160d5d574ea6b58aeb1566','68e155736946f80bc21c8001142c52354108af5305fda5f83ebc0ba85d3c0744','581526f823e6c048b1c969b8a060f7c5d04d45435328473aafeaa6557638775d'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684','Sign26DirectPolynomialBridge':'6f528a24eb7309ad9cea14501f0160ea5c092d9b4c2bf6908a1e6b83aee2acc3'}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,100,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 assert (A/f'{n}-compile.txt').read_bytes()==b''
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-endpoint-import-diagnostic-prelaunch-frontier-independent/check.py';assert H(pre)=='78b65b6f03acb26fb4a384549847ed567a4f436f1abed5550d44275b5f133e32';up=D/'reviews/nine-sharing-sign26-concrete-polynomial-bridge-terminal-frontier-independent/check.py';assert H(up)=='fd473ee75a9b02210da1c3d6d9b57d4fac253bfca1b64bae131fea5b009abd6e';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':50716,'stages':3,'guards':350,'links':1366,'scope':'framework, bridge and combined import-only diagnostics; no endpoint theorem or precise cause'},sort_keys=True,indent=2))
