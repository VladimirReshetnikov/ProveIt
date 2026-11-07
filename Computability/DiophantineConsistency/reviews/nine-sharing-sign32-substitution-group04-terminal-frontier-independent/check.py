#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group04-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-substitution-group04-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='315f2b521e9b70963d4a3c362f0925cd2fd2c43c65e8da76c17401a916996669' and sha(A/'outer-result.json')=='f243a081a07de182f4ab71519fbc89e9a1fde6ec56e76806ab61b638cf5ca6a0'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(8748,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1063 and s['runner_sha256']==sha(P/'run.py')=='8a43b1b662beee16c80a9daa79533dfb0e1869f5885b22bdb1461b0ece16cf79' and s['base_state_sha256']=='5f9d1eb3c891c1ca88357e2b2d20e5c07ad6a8130318bb19075f714b0f41c875'
r=s['rows'][0];name='Sign32Substitution04';source='0a4fb6825ff0d966a64e63e4f36c5b83198a5c1b6a39b0b57a31553f77783d9b';obj='703aa1775cc8535a65bce0e860c0e78858c4ffd7dbd9a0e1aae657acb07907de';assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==100
assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'error:|sorryAx',log);assert log.count('warning:')==3 and log.count('Variable name `p` is not explicitly referenced.')==2 and log.count('This simp argument is unused:')==1
for n in ('N1','gap','tau'):
 for t in ('old_'+n+'_row','new_'+n+'_row'):assert f"'DiophantineConsistency.Sign32Substitution04.{t}' depends on axioms: [propext]" in log
 assert re.search(r"'DiophantineConsistency\.Sign32Substitution04\."+n+r"_eval' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
v=r['dependencies']['DiophantineConsistency.Sign32Substitution03'];assert v['sha256']=='67843f316c66191e885a21ecacddd883639a759e5efcd3c2b0aa0307f6590b78' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-sharing-sign32-substitution-group04-prelaunch-frontier-independent';assert sha(R/'check.py')=='fc10a18d6a54d8818c659f0e235b465eecb4c8a03d80c4b2dc3b5eda973995f2' and sha(R/'result.json')=='00ebdb11bc26b84708ff471436d456d88705b5aade4cf073d0d9155100294a97'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':8748,'stages':1,'guard_slots':100,'overlay_links':1063,'scope':'N1/gap/tau old/new row and same-valuation lift evaluations only; no Lean replay or full bridge'},indent=2,sort_keys=True))
