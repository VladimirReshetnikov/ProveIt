#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group03-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-substitution-group03-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='5f9d1eb3c891c1ca88357e2b2d20e5c07ad6a8130318bb19075f714b0f41c875' and sha(A/'outer-result.json')=='ead259b46e16379061669266354b485038c06f97c81e079825afe834fc64ccea'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(21496,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1062 and s['runner_sha256']==sha(P/'run.py')=='9d60e54966723d6ac0d03e36dc3f0b46c74f802e1139efc4fa02f85f8f692e36' and s['base_state_sha256']=='39f28826970b5aa1ec89760bb4a58acc59513e8022069321e78896a24e60f00c'
r=s['rows'][0];name='Sign32Substitution03';source='82f1c8b6a79d091b28ecc4bf1a846a531d38d430bc91a1f5736ab0cf5903a810';obj='67843f316c66191e885a21ecacddd883639a759e5efcd3c2b0aa0307f6590b78';assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==100
assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'error:|sorryAx',log);assert log.count('warning:')==8 and log.count('Variable name `p` is not explicitly referenced.')==6 and log.count('This simp argument is unused:')==2
for n in ('mainRoot','c2','Dc2'):
 for t in ('old_'+n+'_row','new_'+n+'_row'):assert f"'DiophantineConsistency.Sign32Substitution03.{t}' depends on axioms: [propext]" in log
 assert re.search(r"'DiophantineConsistency\.Sign32Substitution03\."+n+r"_eval' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
v=r['dependencies']['DiophantineConsistency.Sign32Substitution02'];assert v['sha256']=='ac0d8c0012a70f9579899ac8b7bcbc307280f1affa46195e0ce231588ab1af26' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-sharing-sign32-substitution-group03-prelaunch-frontier-independent';assert sha(R/'check.py')=='3e047f65fc6bdd1d06514d68105d13867a859a42d1f3dbadc6972e0dc7f3834a' and sha(R/'result.json')=='8a8cfeaf8fa962d73ce247815a092e092cc94716328c396825f47d01594c3854'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':21496,'stages':1,'guard_slots':100,'overlay_links':1062,'scope':'mainRoot/c2/Dc2 old/new row and same-valuation lift evaluations only; no Lean replay or full bridge'},indent=2,sort_keys=True))
