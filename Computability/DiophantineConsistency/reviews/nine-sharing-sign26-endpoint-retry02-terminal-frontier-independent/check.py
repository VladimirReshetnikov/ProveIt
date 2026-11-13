#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-endpoint-retry02';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-endpoint-retry02-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='7a9bb2d8a670eb5f29c6a77535f66a366099d4857441b724fec45d54c1f90498' and H(A/'outer-result.json')=='077925233d5308ac5cf8443697f77e6ecf77045f7f69f165e21a1744bcca0a51';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'],o['state_sha256'])==(78127,0,H(A/'state.json'))
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1366 and s['runner_sha256']==H(P/'run.py')=='7cd5f3b46e87df7dea69765fb2d0799510c5284092d30973d0d6a7f6fa6a15ed'
names=['Sign26NativeExpression','Sign26DirectNative','Sign26DirectStandard','Sign26DirectTranslated'];objs=['6f3cfe003446e5462e3837744e402b44b50839a496b7937905e7e1571e59291e','87c14bbdecb1256eef6396414c99dfd588807160be7259521b3711ae4cd303f3','8562a6498502445fd4350630137ce559c4a057f59cea75e6db78a3ebd001c719','0380df2c65ba12f3305300c83d6ba41c3e7639452616324bc92ee24d4db0301d'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign26DirectPolynomialBridge':'6f528a24eb7309ad9cea14501f0160ea5c092d9b4c2bf6908a1e6b83aee2acc3','IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684','IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19',**dict(zip(names,objs))}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,150,150,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log;th=['expression_bridge','native_equivalence','standard_equivalence','standard_translated_equivalence'][i];assert f"'DiophantineConsistency.Sign26DirectIPRA.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-endpoint-retry02-prelaunch-frontier-independent/check.py';assert H(pre)=='d2c4f7104482f0a4b510ee191898077b07bf3772868c28b5a4a9ffa6ef89ef55';up=D/'reviews/nine-sharing-sign26-concrete-polynomial-bridge-terminal-frontier-independent/check.py';assert H(up)=='fd473ee75a9b02210da1c3d6d9b57d4fac253bfca1b64bae131fea5b009abd6e';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':78127,'stages':4,'guards':500,'links':1366,'scope':'native, standard and translated direct Fin26 endpoints; no nine-variable Jones, Lean degree or JSON binding'},sort_keys=True,indent=2))
