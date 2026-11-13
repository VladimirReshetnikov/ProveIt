#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-forward-assembly-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-forward-assembly-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='e2459efda6f64202fe1734245697b90317b0e34f8294827a15726c5432a8f2e8' and sha(A/'outer-result.json')=='c8b4c77af15d81acea36d14b6a416e05c599083c9cd4ba810d87231aa27f1190';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(70132,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1067 and s['runner_sha256']==sha(P/'run.py')=='700bba88ee4a579c03c1e48e13787280ae930520db6275a0132086b0bb534046' and s['base_state_sha256']=='16c11717247ef84a52869c265d9e5264e5297993da9020ed1743ac18cb63c176'
objs=['b86d87d52b519dcd62fab1c195999954871fc22fcb1f1b1b53d476e39a483d37','731d00d16252165e2a75465df7ef0197937d3811bf5467669b757970b126d21f','df5831ba83aad3f09ae38b78ae5dc877d39cf23099ae5e3f72e2a048cd85ea1a','a31790adc97b9b51b6b5c9e2f3246540e82ff87f4137637569f25849120f7686'];sources=['7b10cc2caeaa064ce01c95bf6fde1cff3d3f4e3f8c9baf08fcc7e05a8f523525','68e71940d4eb7a56ab823e9f5473a202ee807fa0e8726d34f66517d7f8615274','10824e56a20598cf907bb995887ea223b9088c10e8fc844da266d45275fca468','82b4f997ab21a584696b74d8a1dd713a1422ec0feb032f2b4d5b6db826a124a8'];mods=['Sign32ForwardAssembly00','Sign32ForwardAssembly01','Sign32ForwardAssembly02','Sign32ForwardAssemblyAll'];parents=['Sign32Substitution07']+mods[:-1];ph=['45822b140b89fdfc3783c42e3e37f8bdf13a75af9243cd20db1d18b4f177cd67']+objs[:-1];numreports=0
for r,name,obj,source,parent,h in zip(s['rows'],mods,objs,sources,parents,ph):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==100
 src=P/'src/DiophantineConsistency'/f'{name}.lean';assert sha(src)==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 reports=re.findall(r'^#print axioms DiophantineConsistency\.Sign32ForwardAssembly\.(\w+)$',src.read_text(),re.M);numreports+=len(reports)
 for n in reports:
  pattern=r'\[propext\]' if n=='old_rows' else r'\[propext,\s*Classical.choice,\s*Quot.sound\]';assert re.search(r"'DiophantineConsistency\.Sign32ForwardAssembly\."+n+r"' depends on axioms: "+pattern,log),n
 v=r['dependencies']['DiophantineConsistency.'+parent];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert numreports==25
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert sha(P/'survey.py')=='5f443546621c14ed1283aeff03192f0226235b6ff0a6b165faa786515447276e' and sha(P/'providers.json')=='f46e4aad54ea1f5659b671fb6f677f6b9d3bb95098adbd04526125def9d5e987'
survey=subprocess.run([sys.executable,'-I','-S','-B',str(P/'survey.py')],capture_output=True,text=True,timeout=120,check=True);assert not survey.stderr and json.loads(survey.stdout)['producer_rows']==8 and json.loads(survey.stdout)['status']=='PASS'
R=D/'reviews/nine-sharing-sign32-forward-assembly-prelaunch-frontier-independent';assert sha(R/'check.py')=='07c06200edf28ade4fa2c1aab13d42187c3681e0b7b8b9a6439d145ff48ff220' and sha(R/'result.json')=='42cb52c3eedbfb584512a18592a76d5783695a74b91e8a3c645ee3a727591e0e'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':70132,'stages':4,'reports':25,'guard_slots':400,'overlay_links':1067,'scope':'forward sign32→sign33 zero-set implication only; no Lean replay, reverse, concrete port binding or endpoint'},indent=2,sort_keys=True))
