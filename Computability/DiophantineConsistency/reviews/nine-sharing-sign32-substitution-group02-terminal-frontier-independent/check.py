#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group02-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-substitution-group02-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='39f28826970b5aa1ec89760bb4a58acc59513e8022069321e78896a24e60f00c' and sha(A/'outer-result.json')=='87005af7c493a530b7bc9176834ccf042dda8a0b9d3563c7c331db912b0de1b7'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(54307,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1061 and s['runner_sha256']==sha(P/'run.py')=='e012481cd15af7126c7b562bccaa95cb93201dca10b215fc52c981176f3f0948' and s['base_state_sha256']=='5af027544f0007ce03004adb2c47d2d6f45c74c9d44e7c9d74c7204613eb8725'
r=s['rows'][0];name='Sign32Substitution02';source='528f3c02b24dc15bbe41c9de4ce66515643cad080abb9badf255162b053c846c';obj='ac0d8c0012a70f9579899ac8b7bcbc307280f1affa46195e0ce231588ab1af26';assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==100
assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'error:|sorryAx',log);assert log.count('warning:')==8 and log.count('Variable name `p` is not explicitly referenced.')==6 and log.count('This simp argument is unused:')==2
for n in ('kY','ell','Delta'):
 for t in ('old_'+n+'_row','new_'+n+'_row'):assert f"'DiophantineConsistency.Sign32Substitution02.{t}' depends on axioms: [propext]" in log
 assert re.search(r"'DiophantineConsistency\.Sign32Substitution02\."+n+r"_eval' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
v=r['dependencies']['DiophantineConsistency.Sign32Substitution01'];assert v['sha256']=='6452c3a21013bcfd7b3b2a1a40667481de890c70e414d1db7324979c676c6162' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-sharing-sign32-substitution-group02-prelaunch-frontier-independent';assert sha(R/'check.py')=='5c7443ff74295be30831d7d83290d6563a4ec14a25e0d045c94123d0519ada3c' and sha(R/'result.json')=='ed94dd97f1b6362ee554743fe8af47cb4f107a09f905ba30b0809eb56fe8b5f4'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':54307,'stages':1,'guard_slots':100,'overlay_links':1061,'scope':'kY/ell/Delta old/new row and same-valuation lift evaluations only; no Lean replay or full bridge'},indent=2,sort_keys=True))
