#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-output-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-vars-output-check-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='bb9f2230e366894a0f0224b00dadf96a8955991a6a723aee42023f9c8517143d'
assert sha(A/'outer-terminal-author-record.json')=='9786e990c2e0a31ec0e57f9426aa3d368a5f476ae520d7a2590b132f049d189d'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(55387,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1282
assert sha(P/'run.py')==s['runner_sha256']=='b8ee0019e07f2fde1b3e02a4f0ac7724f77bdf1fe19a2abc4a232a837b4b0736'
assert s['base_state_sha256']=='26bc4134282e64e3915acb773730c6c87f2c35ca190074d0e4401fa524165d1d'
objs=['068b76a14eb12512b8a83b72feb31be24e2a8a21977bc76998c3b52ff4b1d4b5']
rows=[('Norm38MacroVarsOutput','4d1240af3ed3a10a9dcc4244e7aa07836816a8bcca632f315a4789a37e6f8f12',100,{'Norm38MacroVarsKc':'cb7a316ae929ac862636d460e7b8da8be066cfd23555be8ee3958f0b0ce4e041'},['recipe_eq_refined'],[])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroVarsOutput\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroVarsOutput.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-vars-output-prelaunch-frontier-independent';assert sha(R/'check.py')=='ccfc881335e762fdd21d9ec1ca4bcadf66c6c9e2bf8f77a3381d418291cf1544' and sha(R/'result.json')=='841c22bdb8950d6282ba37d0092b60966636c00953c2a7901a9dee370afc18f2'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':55387,'stages':1,'guard_slots':100,'overlay_links':1282,'scope':'recipe output equals RefinedPair of symbolic vars with opaque d11 rank; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
