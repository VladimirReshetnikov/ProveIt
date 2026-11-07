#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group05-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-substitution-group05-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='2cb969c66fc1acdc54b9b1f9b0892565c2552419e3b8b82b0142e033a9f395da' and sha(A/'outer-result.json')=='c69fab8bd61b517d1c22b22932c948461f14b13b7a445edf7ce805747ee56c72'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(84568,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1064 and s['runner_sha256']==sha(P/'run.py')=='ff9a5075fe8c4a40a0a1716159f35eec35853c37403c16307eafe238031eefd0' and s['base_state_sha256']=='315f2b521e9b70963d4a3c362f0925cd2fd2c43c65e8da76c17401a916996669'
r=s['rows'][0];name='Sign32Substitution05';source='7b4c774e8857ae7f66ab0bca4f2861c863a3b61d2c305ab0fd575268e2972e35';obj='930990c7e561d5e3c5e2eefb71ab824d51f29f9085cea1ffc92e698d6a892247';assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==100
assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'error:|sorryAx',log);assert log.count('warning:')==4 and log.count('Variable name `p` is not explicitly referenced.')==4 and log.count('This simp argument is unused:')==0
for n in ('N0','Nt','f2'):
 for t in ('old_'+n+'_row','new_'+n+'_row'):assert f"'DiophantineConsistency.Sign32Substitution05.{t}' depends on axioms: [propext]" in log
 assert re.search(r"'DiophantineConsistency\.Sign32Substitution05\."+n+r"_eval' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
v=r['dependencies']['DiophantineConsistency.Sign32Substitution04'];assert v['sha256']=='703aa1775cc8535a65bce0e860c0e78858c4ffd7dbd9a0e1aae657acb07907de' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-sharing-sign32-substitution-group05-prelaunch-frontier-independent';assert sha(R/'check.py')=='89499326334c7ec1174474344c635dbee51abd2e6641c43f3fa3ee30e1555397' and sha(R/'result.json')=='f3551690b7db55618fbc819ddc4baded1832fd7c468905f933522327b27868a7'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':84568,'stages':1,'guard_slots':100,'overlay_links':1064,'scope':'N0/Nt/f2 old/new row and same-valuation lift evaluations only; no Lean replay or full bridge'},indent=2,sort_keys=True))
