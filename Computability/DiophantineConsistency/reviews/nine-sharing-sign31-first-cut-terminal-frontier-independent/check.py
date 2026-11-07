#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-first-cut-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign31-first-cut-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='585e83086a5c4c29e5d8fdfbada9231fc4f8b1e2a1df5bfc2972cd74bad57131' and sha(A/'outer-result.json')=='a1d181e8a8fcbd54f6e821c78feb51ad4e369bd2250f490b0c9c05df797fc15a';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(33357,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1061 and s['runner_sha256']==sha(P/'run.py')=='d7fe4417b384feab95997f2ed721028f5d4fa8d68e4548581139065459d17b6c';r=s['rows'][0];n='Sign31FirstCut';assert r['module']==n and r['source_sha256']=='6200f778872a1fcff0eb184092616d41a0c7fafac59283fc37b67d47b03bbf1c'==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='491d5b244596b4051298ee640a3ec6cb827ca650febd3cf06c25749ee0637e74'==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
for mod,h in {'SharingSign31Squares':'51221006f98f8c12961936fcde04ae86c1d19f084c752d12dac79979255fda60','SharingSign32Squares':'dcf5d8bb132337b5fcdbbcee6b9aac3a9d5a020cd7191be983a67628af43e850'}.items():
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='70e65affb59caa8435bdf928933d8e770edf8a978ba3036e6e5329cedcc42752' and log.count('warning:')==5 and log.count('Variable name `p` is not explicitly referenced.')==5 and 'sorryAx' not in log
for th in ('old_f2_row','old_V_row','new_V_row','old_scaledNs_row','new_scaledNs_row'):assert f"'DiophantineConsistency.Sign31FirstCut.{th}' depends on axioms: [propext]" in ' '.join(log.split())
for th in ('old_f2_zero','V_eval','scaledNs_eval'):assert f"'DiophantineConsistency.Sign31FirstCut.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
old=json.loads((D/'research/nine-sharing-sign32-sextic-candidate-v2/seed.json').read_text())['residuals'][1:];new=json.loads((D/'research/nine-sharing-sign31-sextic-candidate/seed.json').read_text())['residuals'][1:];assert [old[i]['gate'] for i in (14,16,21)]==['f2','V','scaled_Ns'] and [new[i]['gate'] for i in (15,20)]==['V','scaled_Ns']
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':33357,'reports':8,'warnings':5,'guard_slots':150,'overlay_links':1061,'scope':'f2 lift and two affected residual expression-evaluation cuts only; no complete sign31-to-sign32 bridge'},indent=2,sort_keys=True))
