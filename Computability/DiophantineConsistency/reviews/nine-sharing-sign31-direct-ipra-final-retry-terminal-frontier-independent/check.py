#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-direct-ipra-final-retry';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign31-direct-ipra-final-retry-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='63d7430aacedc3935c015f8c474bff37db42f89223aea72cfee2a9e2d0e01d49' and sha(A/'outer-result.json')=='8f68239cc72338c2f109cdd0a5ef120ce55503778d3a656e4d29d5f4ced87ba1';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(52107,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1303 and s['runner_sha256']==sha(P/'run.py')=='7892c52f793560dcde1e3558741a13b58a3909b066f2555b860d3812c8a063fe';names=['Sign31DirectPolynomialBridge','Sign31DirectNative','Sign31DirectStandard','Sign31DirectTranslated'];objects=['85ee7b7c99ca2160163806ac7689f9ff554316a0245a83701d0bb5c13ae1625f','90cc81cab66163b5b2fd16ce225c9d3b6f1cf19665d6bbef7d2f91c96a8eb876','851e1e5856e670c2d41f7b948f3bbff8f399e2009a2efc651cdc0940ad83ef93','9ce870ea59df7011460617d94636f598798e7e1b64b2dc55819e372b56378d76'];m=json.loads((P/'source-manifest.json').read_text())['rows'];th=['polynomialBridge','native_equivalence','standard_equivalence','standard_translated_equivalence']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[150,150,150,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 expected=({'Sign31CurrentExpressionSource':'8e6bf650153fe5ecb5ac162d2e9550835f084af468c734b472af0308c94b58a9','HACurrentEquation2011':'139adc47e8f48eee0df7fe0ab7f996dd675967473e764fdd9036e8d9fab6e6d1'}, {names[0]:objects[0],'IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684'}, {names[1]:objects[1],'IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19'}, {names[2]:objects[2]})[i]
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log and f"'DiophantineConsistency.Sign31DirectIPRA.{th[i]}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
for rel,h in [('nine-sharing-sign31-direct-ipra-final-retry-prelaunch-frontier-independent/check.py','9250d2e5635fb7dfedff535f93800c53ae3d92a96d86e7f5331feda67adc66bd'),('nine-sharing-sign31-direct-ipra-retry01-failure-frontier-independent/check.py','91f59fd0b6fa26b2a82c9a283ffe6a5a099cc15ca37c9f8f40422d24b1b026b8')]:
 p=D/'reviews'/rel;assert sha(p)==h;subprocess.run([sys.executable,'-I','-S','-B',str(p)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':52107,'stages':4,'theorems':th,'guard_slots':550,'overlay_links':1303,'scope':'direct Fin31 endpoint, no Jones application or Lean degree/JSON coefficient binding; partial successful source provider from overall failed attempt'},indent=2,sort_keys=True))
