#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group00-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-substitution-group00-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='8a4e5256c9d3cf0744693452672eed277bdbfdf9414fdaf3833fd56f638c183f' and sha(A/'outer-result.json')=='b81a8be64630cf4698e2c63b799113ce28aca382b0dafd59a87f5afeab1b244a'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(18759,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1059 and s['runner_sha256']==sha(P/'run.py')=='4d3064ac57e10c4e4c2d4e3512147408e53e07861ceec91de569da0a7d1a8fe9' and s['base_state_sha256']=='c5686add774156ad8156cbff8d7619f8eb9dba5c8100a2b58b48b8169def46e0'
r=s['rows'][0];name='Sign32Substitution00';source='22c01a196c3cef5a6a44e7b447b878af54aaad2461b76f10e16821776329db67';obj='a7814634f0e207f4814565e4e4a43010fdd6c8610a1f70869b9b3d05de323b56';assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==100
assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
for t,axioms in [('old_q3_head',r'\[propext\]'),('old_q2_zero',r'\[propext,\s*Classical.choice,\s*Quot.sound\]'),('old_q3_eval',r'\[propext,\s*Classical.choice,\s*Quot.sound\]')]:assert re.search(r"'DiophantineConsistency\.Sign32Substitution00\."+t+r"' depends on axioms: "+axioms,log)
v=r['dependencies']['DiophantineConsistency.SharingSign32Squares'];assert v['sha256']=='dcf5d8bb132337b5fcdbbcee6b9aac3a9d5a020cd7191be983a67628af43e850' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-sharing-sign32-substitution-group00-prelaunch-frontier-independent';assert sha(R/'check.py')=='93f0775b967d7d695347c3732ff690600c599dbd3907c423cf29e03c451f3618' and sha(R/'result.json')=='c548c785306e6548e4bf7d576454b8eaf73fb1ec45713fe556586716df65f221'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':18759,'stages':1,'guard_slots':100,'overlay_links':1059,'scope':'old q3 list head, inserted old q2 zero and old/new q3 eval only; no Lean replay or full bridge'},indent=2,sort_keys=True))
