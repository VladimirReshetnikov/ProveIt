#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group07-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-substitution-group07-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='16c11717247ef84a52869c265d9e5264e5297993da9020ed1743ac18cb63c176' and sha(A/'outer-result.json')=='b3b1ba2daa4649a50fcdd8ea53412321fe7b61c0296e68ba39129922d628cf35'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(92407,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1066 and s['runner_sha256']==sha(P/'run.py')=='d544bd45b77ab7daef9eb66b14457e35212bfff8d2a978aa1b94a4c80a9ce7c4' and s['base_state_sha256']=='772ff46d260973f88b1f770b11838b55c4a81dc0fe2c71b618caa508c56ea41b'
r=s['rows'][0];name='Sign32Substitution07';source='e83dc77bc439b2ee86414616693ad653002244f3dc1613c50c6cb6a3d86ecff1';obj='45822b140b89fdfc3783c42e3e37f8bdf13a75af9243cd20db1d18b4f177cd67';assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==100
assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'error:|sorryAx',log);assert log.count('warning:')==12 and log.count('Variable name `p` is not explicitly referenced.')==8 and log.count('This simp argument is unused:')==4
for n in ('normalizedS2','V2minusY2','Na','scaledNs'):
 for t in ('old_'+n+'_row','new_'+n+'_row'):assert f"'DiophantineConsistency.Sign32Substitution07.{t}' depends on axioms: [propext]" in log
 assert re.search(r"'DiophantineConsistency\.Sign32Substitution07\."+n+r"_eval' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
v=r['dependencies']['DiophantineConsistency.Sign32Substitution06'];assert v['sha256']=='2f32d2e0277992a7489ce32e31448bb6f0dcac9d710c6939aab95737bc17d41f' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-sharing-sign32-substitution-group07-prelaunch-frontier-independent';assert sha(R/'check.py')=='9e2c6d4ec5cacadd76743c22d9dbaeb4fe67a9add42003f45113df15e14ea63b' and sha(R/'result.json')=='391c449040bbb62c3dad563b416b795e4b0deaff10e48635b0f7f404f073ccd7'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':92407,'stages':1,'guard_slots':100,'overlay_links':1066,'scope':'normalizedS2/V2minusY2/Na/scaledNs old/new row and same-valuation lift evaluations only; no Lean replay or full bridge'},indent=2,sort_keys=True))
