#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-checkpoint42-dm-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-checkpoint42-dm-check-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='66b0e34af2cae85fb44fce028f6245fbdbc2f9ea8eb8556b12d173d1c9f8265d'
assert sha(A/'outer-terminal-author-record.json')=='f01f810a7268a25b9bee6ff731b75189fa996cf2d66e1ca6a7826e563141f64b'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(61421,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1269
assert sha(P/'run.py')==s['runner_sha256']=='fcdec63095f78da4ad4e6f44b64d062634d04d4165b9bd317b6ce5ba4e96bea6'
assert s['base_state_sha256']=='79be3f29dbea9eadb6616763c863f50c61528f678804229d5b3e0e1c19c73981'
objs=['9b380ad4f9305d787de1520d9466d9876e72f04f26a4df5ea99b1c2438fe1d52','d7e21e6b765a1a796c0f87165394188f19bc25df619a32fd7d9d8780948c803a']
rows=[('Norm38MacroDmInputs','06d62b29d3c043dab0b50c94953774d5a53358af62709c09100748533f86dfca',150,{'Norm38MacroCdValue':'6d243292a8fca880882143a751e5daadb0cdfcc334a60ba880481c42f67325e2','Norm38MacroCheckpoint41to45':'d0dc8713317ad6f6b829c3776d740169273d9abecbf5a344489c148fb04cb565'},['d41_K_value','d41_Y_value'],[]),('Norm38MacroDmValue','f10360f9d27362cfb8c4ae8c0f17f760c6e1316084508862af01607f982b1e9b',150,{'Norm38MacroDmInputs':objs[0],'Norm38MacroDependentDmKc':'9c6fa4a8df1d1376528fb8ae07ed1648572cf9e0534bb4d2d6cfc897cb157e59'},['d42_Dm_value'],[])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointDm\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroCheckpointDm.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-checkpoint42-dm-prelaunch-frontier-independent';assert sha(R/'check.py')=='e17506096758c6e4963d8153c9dc7e76b0f7cb862ffa8a6abfc11237a0422ec4' and sha(R/'result.json')=='438e6c4596a6178eaf1199924230f53a4b0a3d446e97173ee612b4fc4a73f50f'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':61421,'stages':2,'guard_slots':300,'overlay_links':1269,'scope':'symbolic Dm at d42 and K/Y at d41; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
