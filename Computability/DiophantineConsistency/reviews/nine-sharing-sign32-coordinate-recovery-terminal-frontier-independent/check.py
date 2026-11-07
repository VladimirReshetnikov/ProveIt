#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-coordinate-recovery-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-coordinate-recovery-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='6821419df5a6b027d337cf5a712b00e1e11a977e3456d68cf8d552e4c9c9b5ae' and sha(A/'outer-result.json')=='52a3ec036b10defa3c2dc58e09cba09cea1a4e745e380abe0d7ac2c8545a0174';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(23846,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1067 and s['runner_sha256']==sha(P/'run.py')=='878b8062c9701cab468d2edf3a82a6ee60d689f0684dfa4a631218e61c9b2970' and s['base_state_sha256']=='16c11717247ef84a52869c265d9e5264e5297993da9020ed1743ac18cb63c176'
objs=['9b312200ab6271072de40beebf37f019996e1ffed27e64c48828ea7da70c85b6','6541cac0540b2f3b2f07edd38902fc47bac55adbdc17e24b362d9e80dc9859d5'];sources=['71140c5eaffe5f0ff72488c4c76bcb3e03dd734b2f4a5078b8433f4ef2532b11','df139121e3ac4acd424a1ca3be914012ea9a974540e5d4d0a1cbe95a871e7d0c'];mods=['Sign32CoordinateRecover','Sign32CoordinateReconstruct'];parents=['Sign32Substitution07','Sign32CoordinateRecover'];ph=['45822b140b89fdfc3783c42e3e37f8bdf13a75af9243cd20db1d18b4f177cd67',objs[0]];numreports=0
for r,name,obj,source,parent,h in zip(s['rows'],mods,objs,sources,parents,ph):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==100
 src=P/'src/DiophantineConsistency'/f'{name}.lean';assert sha(src)==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 reports=re.findall(r'^#print axioms DiophantineConsistency\.Sign32CoordinateRecover\.(\w+)$',src.read_text(),re.M);numreports+=len(reports)
 for n in reports:
  pattern=r'\[propext,\s*Classical.choice,\s*Quot.sound\]';assert re.search(r"'DiophantineConsistency\.Sign32CoordinateRecover\."+n+r"' depends on axioms: "+pattern,log),n
 v=r['dependencies']['DiophantineConsistency.'+parent];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert numreports==2
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert sha(P/'survey.py')=='5f443546621c14ed1283aeff03192f0226235b6ff0a6b165faa786515447276e' and sha(P/'providers.json')=='f46e4aad54ea1f5659b671fb6f677f6b9d3bb95098adbd04526125def9d5e987'
survey=subprocess.run([sys.executable,'-I','-S','-B',str(P/'survey.py')],capture_output=True,text=True,timeout=120,check=True);assert not survey.stderr and json.loads(survey.stdout)['producer_rows']==8 and json.loads(survey.stdout)['status']=='PASS'
R=D/'reviews/nine-sharing-sign32-coordinate-recovery-prelaunch-frontier-independent';assert sha(R/'check.py')=='690e537ca6e14fd4640d6f9f2b4b36f3b13bd047fbefdb3603fab8fc30d6f960' and sha(R/'result.json')=='667ff142b7d79ab5d0420af4d7399bf2c830f064789e8aa4a74af271a3292835'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':23846,'stages':2,'reports':2,'guard_slots':200,'overlay_links':1067,'scope':'q² coordinate recovery and lift(drop(v))=v under hp0 and old seed zero; no Lean replay or reverse seed implication'},indent=2,sort_keys=True))
