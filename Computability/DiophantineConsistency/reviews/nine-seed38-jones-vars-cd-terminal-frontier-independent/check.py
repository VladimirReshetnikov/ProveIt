#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-cd-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-vars-cd-check-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='71450c1f5044e62f3b2a10eab7d443b3cf4b6c07f5133d29060b9fe43be71de4'
assert sha(A/'outer-terminal-author-record.json')=='c5966ee92dab05e2a1a521bbd79bcb68664cdd075541ebc68f1041e149686626'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(90536,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1275
assert sha(P/'run.py')==s['runner_sha256']=='9436d56e73eb11bd1792f929d76e9ce5ecbbc528eb347dcd05338d4f64213fa8'
assert s['base_state_sha256']=='3723d26904e39f7606b3a3f844014033756e1b203ffe1f3aa452dde6f7947884'
objs=['1dfc9cbdefc4f7ec437dd2acd3b09bd1668897e263bdfa96c8ffe5182e349138']
rows=[('Norm38MacroVarsCd','fa636d77fbc32142d8aa67c3d556cb970cd536e79a964e57c88a64a538253c79',100,{'Norm38MacroVarsBd':'04918fb03433f8f26c2cf52f792235c47b4a7e9687dd967182f52a340d64e3f4'},['d41_Cd_eq_dvnd'],[])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroVarsCd\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroVarsCd.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-vars-cd-prelaunch-frontier-independent';assert sha(R/'check.py')=='35a9cf12b2254b173a9f0fdfbb4162ffb501a2a841e1541d0c0875d9e0bb441f' and sha(R/'result.json')=='4c60d898b2ae8412b49dcc7e36da4759b6a4b573838a9655dc715b7f01f20c9a'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':90536,'stages':1,'guard_slots':100,'overlay_links':1275,'scope':'symbolic Cd to vars.dvnd with opaque d11 rank; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
