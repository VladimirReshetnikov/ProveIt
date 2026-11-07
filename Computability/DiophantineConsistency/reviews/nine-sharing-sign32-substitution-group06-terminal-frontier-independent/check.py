#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group06-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-substitution-group06-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='772ff46d260973f88b1f770b11838b55c4a81dc0fe2c71b618caa508c56ea41b' and sha(A/'outer-result.json')=='9cf789df887c33a57e69f82d659cac5909b2f55a94c2b497fc1da08900e1f58a'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(51650,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1065 and s['runner_sha256']==sha(P/'run.py')=='8fbb118c53e530979616c9454def6bef8b5f02fae743ea320c9b223d5cb7c074' and s['base_state_sha256']=='2cb969c66fc1acdc54b9b1f9b0892565c2552419e3b8b82b0142e033a9f395da'
r=s['rows'][0];name='Sign32Substitution06';source='a5fc42f991fbb0b5bc8891a798d7ab04fd692a8708b8e84e76ffe2b0c62a096b';obj='2f32d2e0277992a7489ce32e31448bb6f0dcac9d710c6939aab95737bc17d41f';assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==100
assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'error:|sorryAx',log);assert log.count('warning:')==4 and log.count('Variable name `p` is not explicitly referenced.')==4 and log.count('This simp argument is unused:')==0
for n in ('cTminusR','V','normalizedS'):
 for t in ('old_'+n+'_row','new_'+n+'_row'):assert f"'DiophantineConsistency.Sign32Substitution06.{t}' depends on axioms: [propext]" in log
 assert re.search(r"'DiophantineConsistency\.Sign32Substitution06\."+n+r"_eval' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
v=r['dependencies']['DiophantineConsistency.Sign32Substitution05'];assert v['sha256']=='930990c7e561d5e3c5e2eefb71ab824d51f29f9085cea1ffc92e698d6a892247' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-sharing-sign32-substitution-group06-prelaunch-frontier-independent';assert sha(R/'check.py')=='14ea268fc2b27c7efb2231ff53c311c1dcce53a563850ed419b0cb29eeaae5cf' and sha(R/'result.json')=='c773aac7af47ad44d3cf02b817c3b988d88308c2ccb207a57710d7617eee1a3c'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':51650,'stages':1,'guard_slots':100,'overlay_links':1065,'scope':'cTminusR/V/normalizedS old/new row and same-valuation lift evaluations only; no Lean replay or full bridge'},indent=2,sort_keys=True))
