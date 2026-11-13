#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group01-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-substitution-group01-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='5af027544f0007ce03004adb2c47d2d6f45c74c9d44e7c9d74c7204613eb8725' and sha(A/'outer-result.json')=='a79c70c3feda20ebe537d5728ad687d6b054e2141f5d01f5e41d90831f17c964'
o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(29038,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1060 and s['runner_sha256']==sha(P/'run.py')=='0f5a58ea3285e4995261f38ffa222de8467608c1ad62ff55148859df0fab574a' and s['base_state_sha256']=='8a4e5256c9d3cf0744693452672eed277bdbfdf9414fdaf3833fd56f638c183f'
r=s['rows'][0];name='Sign32Substitution01';source='fac10f7a53fb99ee6b7017998bec5fa2a37a5900672b1a9b6216f049e6a84efa';obj='6452c3a21013bcfd7b3b2a1a40667481de890c70e414d1db7324979c676c6162';assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==100
assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'error:|sorryAx',log);assert log.count('warning:')==6 and log.count('Variable name `p` is not explicitly referenced.')==4 and log.count('This simp argument is unused:')==2
for n in ('X','Y','E'):
 for t in ('old_'+n+'_row','new_'+n+'_row'):assert f"'DiophantineConsistency.Sign32Substitution01.{t}' depends on axioms: [propext]" in log
 assert re.search(r"'DiophantineConsistency\.Sign32Substitution01\."+n+r"_eval' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
v=r['dependencies']['DiophantineConsistency.Sign32Substitution00'];assert v['sha256']=='a7814634f0e207f4814565e4e4a43010fdd6c8610a1f70869b9b3d05de323b56' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-sharing-sign32-substitution-group01-prelaunch-frontier-independent';assert sha(R/'check.py')=='e3d79340f1261024af74c35a5dfa758de20b7f6c77f09cb5fb0c23794103153f' and sha(R/'result.json')=='a5993326cbf0b904cef93bf0c8736e30e35133ef404deafeccff708b01b79176'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':29038,'stages':1,'guard_slots':100,'overlay_links':1060,'scope':'X/Y/E old/new row and same-valuation lift evaluations only; no Lean replay or full bridge'},indent=2,sort_keys=True))
