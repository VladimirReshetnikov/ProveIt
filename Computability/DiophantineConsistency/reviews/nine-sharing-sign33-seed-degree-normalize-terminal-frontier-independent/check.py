#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-seed-degree-normalize-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-seed-degree-normalize-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='b065c59adc2d926e48462fa8eeb8af4024f4e82784d034bc28b0b3099d181945'
assert h(a/'outer-observation.json')=='2a3fe31aeca9daf623bca70b8bc47128adaee8b1343096da3206e8689eb3ade5'
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(56200,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3
objects=['f4aac073a2cacfe0886b97e4b1894f02d1c64e3537ac2e1a9f141b4e5e517867','c5cd689e4ff51d433662373fcc83d189e57c5892f59f8d4a62d2383d4cad0718','4e315b2439ee1f8133cd358c3ff8031bad9b23efbaf3907ef35529c81c859527']
names=['SharingSeed33Normalize','SharingSeed33Weighted','SharingSeed33Degree'];reports=[['firstResidual_zeroWitness','eval_sumSquares_nonneg','seed_normalized'],['seed_weightedDegree'],['seed_degree']];warn=[1,1,0]
for r,n,obj,rs,w in zip(s['rows'],names,objects,reports,warn):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj
 assert h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert log.count('warning:')==w and 'error:' not in log and 'sorryAx' not in log
 for t in rs:
  axioms='[propext, Quot.sound]' if t=='firstResidual_zeroWitness' else '[propext, Classical.choice, Quot.sound]'
  assert "'DiophantineConsistency.SharingSeed33."+t+"' depends on axioms: "+axioms in log
 depname='DiophantineConsistency.SharingSeed33Weighted' if n=='SharingSeed33Degree' else 'DiophantineConsistency.SharingSeed33Syntax';dep=r['dependencies'][depname];expected=objects[1] if n=='SharingSeed33Degree' else 'd8d70064be0d7fa609b92a8b51648b6e817096886e0671f37d64271f05e21be0';assert dep['sha256']==expected and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':expected}
 assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1056
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
review=d/'reviews/nine-sharing-sign33-seed-syntax-frontier-independent/check.py';assert h(review)=='934ac9b2b352d19a8b0cef7d04f40270a44fd4a9e428dc50df7bc05123a3a245';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS','author_recorded_outer_session':56200,'stages':3,'direct_guard_slots':300,'overlay_links':1056,'scope':'symbolic normalization and degree upper bound; no Lean replay'},sort_keys=True,indent=2))
