#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-reverse-assembly-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign32-reverse-assembly-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='d6aba2d04a256ca74d614197579dee08e53abada73152a66573c4d88e23152a9' and sha(A/'outer-result.json')=='e94ef40a1f58531dd35ab0b02d1aa4f1682f3aa65eb89cf4fa76dabf3f79fea5';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(36474,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1069 and s['runner_sha256']==sha(P/'run.py')=='6ee167bb1003f83708923037e0107378d7fdd533d3ad572daeb47a16824ae07b' and s['base_state_sha256']=='6821419df5a6b027d337cf5a712b00e1e11a977e3456d68cf8d552e4c9c9b5ae'
objs=['1040877d26591e70cf8163d1a966a5630ff452c0cd7a156d6e0848abc28934cc','d89cfd709f4983ea66fc11b1814954bcf6a0b2921f179b2a567edb8862a18467','92fe77c0c5355c4e8161abb6eef5962d37fc34e9f0585f0a97fdf6123f92c129','eb9f10c3511e763140f514d6ee298fc456601499652dbe85dcb5df70c69f1bb3'];sources=['51922775c5abdb1765209e95212ccce6d009fe626442b0d7799260f65345d0e6','affc7e9ad7e8b836ceee6def5e26804a5b2c0528c22fcf22fbbcbf8cd69e1cb2','5444f6f2a58e21c515f4ca8bb67660c61813fa6ae31d831732093eea9abff2af','1f257ea723c607b5774641886ff9499030dd7428c62b6bce84897036561cfc12'];mods=['Sign32ReverseAssembly00','Sign32ReverseAssembly01','Sign32ReverseAssembly02','Sign32ReverseAssemblyAll'];parents=['Sign32CoordinateReconstruct']+mods[:-1];ph=['6541cac0540b2f3b2f07edd38902fc47bac55adbdc17e24b362d9e80dc9859d5']+objs[:-1];numreports=0
for r,name,obj,source,parent,h in zip(s['rows'],mods,objs,sources,parents,ph):
 assert r['module']==name and r['source_sha256']==source and r['object_sha256']==obj and len(r['direct_guard'])==100
 src=P/'src/DiophantineConsistency'/f'{name}.lean';assert sha(src)==sha(O/'src/DiophantineConsistency'/f'{name}.lean')==source and sha(O/'lib/DiophantineConsistency'/f'{name}.olean')==obj
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{name}-{phase}.txt')==sha(O/f'{name}-{phase}.txt')==o['logs'][f'{name}-{phase}.txt']==v['log_sha256']
 log=(A/f'{name}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',log)
 reports=re.findall(r'^#print axioms DiophantineConsistency\.Sign32ReverseAssembly\.(\w+)$',src.read_text(),re.M);numreports+=len(reports)
 for n in reports:
  pattern=r'\[propext\]' if n=='new_rows' else r'\[propext,\s*Classical.choice,\s*Quot.sound\]';assert re.search(r"'DiophantineConsistency\.Sign32ReverseAssembly\."+n+r"' depends on axioms: "+pattern,log),n
 v=r['dependencies']['DiophantineConsistency.'+parent];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert numreports==25
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert sha(P/'survey.py')=='c188b08dd16285174f5c88952e63f5b9b927f0a1ea599f0002672c7040fb4304' and sha(P/'providers.json')=='f46e4aad54ea1f5659b671fb6f677f6b9d3bb95098adbd04526125def9d5e987'
survey=subprocess.run([sys.executable,'-I','-S','-B',str(P/'survey.py')],capture_output=True,text=True,timeout=120,check=True);assert not survey.stderr and json.loads(survey.stdout)['producer_rows']==8 and json.loads(survey.stdout)['status']=='PASS'
R=D/'reviews/nine-sharing-sign32-reverse-assembly-prelaunch-frontier-independent';assert sha(R/'check.py')=='44c3f8523adc91a7dd3eeafb420208bb94a9afff4f9bb760240de96e63aee047' and sha(R/'result.json')=='825aea704740c1983d00ac74c815a2498f2566ab0c5155bfa2516a8738e5d4d0'
print(json.dumps({'status':'PASS_TERMINAL_POINT_CHECK','author_recorded_outer_session':36474,'stages':4,'reports':25,'guard_slots':400,'overlay_links':1069,'scope':'reverse sign33→sign32 zero-set implication only; no Lean replay, concrete port binding or endpoint'},indent=2,sort_keys=True))
