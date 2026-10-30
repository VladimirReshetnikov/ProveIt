"""Rebuild a one-sided 85 HA suffix on one independently checked 86 HA snapshot.

This deliberately retains the old parent/HA/ZF/Foundation/package source
boundary; it does not claim a full current-source closure or a converse.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');SRC=R/'Computability/DiophantineConsistency/Lean';D=R/'Computability/DiophantineConsistency/research/adaptive-gap85';P=Path('/tmp/ha86-focused-extension-0tthss1z');Q=Path('/tmp/ha87-focused-validator-rebase-3tvgyxbr');PKG=Path('/tmp/ha87-full-source-jrvxi6bb');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ps=read(P/'state.json');qs=read(Q/'state.json');assert ps['status']==qs['status']=='PASS';ph=sha(P/'state.json');qh=sha(Q/'state.json');assert ps['ha87_author_state_sha256']==qh;packageh=sha(PKG/'state.json');assert packageh==qs['package_audit_state_sha256'];pih=sha(P/'providers.json');assert pih==ps['project_provider_inventory_sha256'];C=D/'candidate.json';G=D/'generate_literal.py';ch=sha(C);gh=sha(G);assert ch=='c2c2e1bbb267bdc155536c5b3df9641f8faff97dab4b549a1d514d671ebdea00'
seen=set();build=[];boundary=[]
def visit(n):
 if n in seen:return
 seen.add(n);obj=P/'lib'/(n.replace('.','/')+'.olean')
 if obj.is_file():boundary.append(n);return
 p=SRC/(n.replace('.','/')+'.lean')
 if not p.is_file():boundary.append(n);return
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for x in line[7:].split():visit(x)
 build.append(n)
visit('DiophantineConsistency.HAAdaptiveGap85ImplicationChecks');assert len(build)==10 and build[-1]=='DiophantineConsistency.HAAdaptiveGap85ImplicationChecks';snap={n:sha(SRC/(n.replace('.','/')+'.lean')) for n in build};inventory={}
for top in (P/'lib').iterdir():
 if top.name in ('Foundation','Mathlib') or not top.is_dir():continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   if f.endswith('.olean'):
    p=Path(root)/f;inventory[str(p.relative_to(P/'lib'))]={'path':str(p.resolve()),'sha256':sha(p)}
for n in boundary:
 if n.startswith('DiophantineConsistency.'):assert n.replace('.','/')+'.olean' in inventory,n
w=Path(tempfile.mkdtemp(prefix='ha85-implication-snapshot-'));(w/'logs').mkdir();shutil.copyfile(__file__,w/'driver.py');(w/'providers.json').write_text(json.dumps(inventory,indent=2,sort_keys=True)+'\n');ih=sha(w/'providers.json');lib=w/'lib';lib.mkdir()
for top in (P/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   p=Path(root)/f;q=lib/p.relative_to(P/'lib');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(p.resolve())
for n in build:shutil.copyfile(SRC/(n.replace('.','/')+'.lean'),w/'logs'/(n.split('.')[-1]+'.lean'))
scratch=w/'generated/Computability/DiophantineConsistency/research/adaptive-gap85';scratch.mkdir(parents=True);(w/'generated/Computability/DiophantineConsistency/Lean/DiophantineConsistency').mkdir(parents=True);shutil.copyfile(G,scratch/'generate_literal.py');shutil.copyfile(C,scratch/'candidate.json');state={'status':'RUNNING','private':str(w),'parent_state_sha256':ph,'parent_parent_state_sha256':qh,'package_state_sha256':packageh,'parent_provider_inventory_sha256':pih,'selected_provider_inventory_sha256':ih,'selected_provider_count':len(inventory),'parent_outputs':len(ps['records']),'parent_parent_outputs':len(qs['records']),'candidate_sha256':ch,'generator_sha256':gh,'source_sha256':snap,'build_order':build,'direct_boundaries':boundary,'records':[],'scope':'One-sided HA implication for the exact 85 shifted literal on a coherent independently replayed 86 HA snapshot, with nine current-source proof modules plus checks. Parent adaptive/HA/ZF/Foundation/package source ancestry remains historical; no reverse 85 bound, equivalence, or full source-current closure is claimed.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
def auth():
 return sha(P/'state.json')==ph and sha(Q/'state.json')==qh and sha(PKG/'state.json')==packageh and sha(P/'providers.json')==pih and sha(C)==ch and sha(G)==gh and sha(w/'providers.json')==ih and all(sha(SRC/(n.replace('.','/')+'.lean'))==h for n,h in snap.items()) and all(sha(x['path'])==x['sha256'] for x in inventory.values()) and all(sha(P/'lib'/(r['name'].replace('.','/')+'.olean'))==r['object_sha256'] and sha(P/'logs'/(r['name'].split('.')[-1]+'.log'))==r['log_sha256'] for r in ps['records']) and all(sha(Q/'lib'/(r['module'].replace('.','/')+'.olean'))==r['object_sha256'] and sha(Q/'logs'/r['log_file'])==r['log_sha256'] for r in qs['records'] if r.get('verified'))
save();print('PRIVATE',w,'MODULES',len(build),'PROVIDERS',len(inventory),flush=True)
try:
 assert auth()
 with (w/'logs/generator.log').open('w') as f:gcode=subprocess.run(['python3',str(scratch/'generate_literal.py')],cwd=R,stdout=f,stderr=subprocess.STDOUT).returncode
 gen=w/'generated/Computability/DiophantineConsistency/Lean/DiophantineConsistency/AdaptiveGap85Literal.lean';state.update(generator_exit=gcode,generator_log_sha256=sha(w/'logs/generator.log'),generated_source_sha256=sha(gen) if gen.is_file() else None);save();assert gcode==0 and sha(gen)==snap['DiophantineConsistency.AdaptiveGap85Literal']
 env=dict(os.environ,LEAN_PATH=':'.join([str(lib),str(PKG/'package-lib')]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in build:
  short=n.split('.')[-1];src=SRC/(n.replace('.','/')+'.lean');out=lib/(n.replace('.','/')+'.olean');log=w/'logs'/(short+'.log');tim=w/'logs'/(short+'.time');assert not out.exists() and sha(src)==snap[n];cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M8000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',short,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim),'command':cmd,'object_sha256':sha(out) if out.is_file() else None};state['records'].append(row);save();print('DONE',short,code,flush=True)
  if code:raise RuntimeError(n)
 assert auth() and all(sha(w/'logs'/(r['name'].split('.')[-1]+'.lean'))==r['source_sha256'] and sha(lib/(r['name'].replace('.','/')+'.olean'))==r['object_sha256'] and sha(w/'logs'/(r['name'].split('.')[-1]+'.log'))==r['log_sha256'] for r in state['records']);state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
