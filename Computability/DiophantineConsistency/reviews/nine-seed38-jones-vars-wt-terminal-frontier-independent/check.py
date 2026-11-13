#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-wt-check';A=P/'attempt01';O=Path('/tmp/nine-seed38-jones-vars-wt-check-20261106'); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='22a3472ca55b1681b4fe4f51ca43e4ca97f3b054d52d6da3ffa75b4482575514'
assert sha(A/'outer-terminal-author-record.json')=='ec274cf844c3cf4a107849fd0329edc8b11008db7f9e7cf915e685edad28a1a4'
o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(70406,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1278
assert sha(P/'run.py')==s['runner_sha256']=='ad02f4a2115a512174c6a4d741d0a80f37789218c9202b69612d484f372869d3'
assert s['base_state_sha256']=='8643b1814c0c4ef4513f5b8e39c9ca74eb45c1c0f5da7febeaacb1199d17824e'
objs=['323e402358e688814c1b57d4c13d34d44620713a1a39e4ce82aeadee13fe1232','c1317d8835be2a9775fda42b676fb4f117206ef456bcd57af9fa53df1dd32347']
rows=[('Norm38MacroVarsWt0','8798255354b32257ba2f0daaeee61e71d7fc32ea79238a0b5d7347fadab50f45',100,{'Norm38MacroVarsRad1':'76684ed48a14cc0329ccd3000599e76b1dfcc420aae03bfb8a6ff3b711850fc2'},['d41_V0_eq_wt0'],[]),('Norm38MacroVarsWt1','4c438960a38a6e12ce16cc3d0d20e4d4e16f16da68fa8ae45b7c591be780a056',100,{'Norm38MacroVarsWt0':objs[0]},['d41_V1_eq_wt1'],[])]
for r,obj,(name,source,count,expected,std,pure) in zip(s['rows'],objs,rows):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==count
 assert sha(P/'src/DiophantineConsistency'/f'{name}.lean')==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 for t in std: assert re.search(r"'DiophantineConsistency\.Norm38MacroVarsWt\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for t in pure: assert f"'DiophantineConsistency.Norm38MacroVarsWt.{t}' does not depend on any axioms" in log
 for mod,h in expected.items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
R=D/'reviews/nine-seed38-jones-vars-wt-prelaunch-frontier-independent';assert sha(R/'check.py')=='16bc7fe6a12307567fb546bc92fc92b84b7fd4dd8a81c773eb3c3d2da8fc542b' and sha(R/'result.json')=='9e3a4124359dece565bbe1d4fb8ed91c0c8cf3e36f7f73879b86432378d903d7'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':70406,'stages':2,'guard_slots':200,'overlay_links':1278,'scope':'symbolic V0/V1 to vars.wt0/wt1; no Lean replay, complete transitive trace, or full formula claim'},indent=2,sort_keys=True))
