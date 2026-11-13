#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-direct-ipra-final-retry01';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-direct-ipra-final-retry01-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='9d55bf18333b09c35318e206be85232886f784a6d92a5e69eef0c3ce238df0dc' and sha(A/'outer-result.json')=='51bcbc8970d50ec151158dc83c990d067f41a3680ce77ab5feea5bc5de116706';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(20251,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1291 and s['runner_sha256']==sha(P/'run.py')=='68e61a95a01df123d1433a9dc38d2cb50e41d74febe03dc01a9cceb629d9e45e';r=s['rows'][0];n='Sign32DirectIPRA';assert r['module']==n and r['source_sha256']=='3e4def38dc06a82d16dcab596fe8606259fccab89f2ced85f02f462bfbb779be'==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='9f93e8ddc4c0986d240bd5e704ac4509f6da5d22dfeb166077c428e350b6dbbf'==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==250
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
for mod,h in {'Sign32CurrentExpressionSource':'e1f97c454d60009f2015aa69d048f328f3d25dde74326f068394debaa4b94876','HACurrentEquation2011':'139adc47e8f48eee0df7fe0ab7f996dd675967473e764fdd9036e8d9fab6e6d1','IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684','IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19'}.items():
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='9f827ec3aa35a36a75389eeebb9d305c0abe062106999c9dab1445eee821bfc9' and 'warning:' not in log and 'sorryAx' not in log
for theorem in ('polynomialBridge','native_equivalence','standard_equivalence','standard_translated_equivalence'):
 assert f"'DiophantineConsistency.Sign32DirectIPRA.{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for rel,h in [('nine-sharing-sign32-direct-ipra-final-retry01-prelaunch-frontier-independent/check.py','cb6ac0fb0cf85e205a0f2f1e891125719b5ac0d3edbeae9b6a666bfd5de4d282'),('nine-sharing-sign32-direct-ipra-final-failure-frontier-independent/check.py','55fa789fc6e724525e75ba563be72faddeb6ad2f95b65d038709d5ec330c71a1')]:
 p=D/'reviews'/rel;assert sha(p)==h;subprocess.run([sys.executable,'-I','-S','-B',str(p)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':20251,'theorems':['polynomialBridge','native_equivalence','standard_equivalence','standard_translated_equivalence'],'axioms':['propext','Classical.choice','Quot.sound'],'guard_slots':250,'overlay_links':1291,'scope':'direct 32-coordinate endpoint; no Lean degree or external JSON/coefficients binding; author-recorded outer exit and inherited transitive/provider caveats'},indent=2,sort_keys=True))
