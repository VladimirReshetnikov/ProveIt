from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';REV=D/'reviews';B=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
PLAN=D/'research/c222-dagperm-runtime-cache-plan-20261027.json'
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def require(x,msg):
 if not x:raise RuntimeError(msg)
def guard():require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
def nested(x):
 if isinstance(x,dict):
  if 'path'in x and'sha256'in x:yield x
  for v in x.values():yield from nested(v)
 elif isinstance(x,list):
  for v in x:yield from nested(v)
def imports(p):
 s=Path(p).read_text();out=[];i=depth=0
 while i<len(s):
  pair=s[i:i+2]
  if depth:
   if pair=='/-':depth+=1;i+=2
   elif pair=='-/':depth-=1;i+=2
   else:out.append('\n'if s[i]=='\n'else' ');i+=1
  elif pair=='/-':depth=1;i+=2
  elif pair=='--':
   while i<len(s)and s[i]!='\n':i+=1
  else:out.append(s[i]);i+=1
 require(depth==0,'balanced comments')
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M)for n in line.split()]))
pins={};observations=0
def check(r):
 global observations
 a=rec(r['path']);require(a['sha256']==r['sha256'],'hash '+r['path']);pins[a['path']]=a;observations+=1;return a
guard();p=Path(tempfile.mkdtemp(prefix='dag-macros-perm222-controller-author-'));lib=p/'lib';lib.mkdir()
state=dict(status='PREFLIGHT',private=str(p),driver=rec(__file__),records=[]);save(p/'AUTHOR.json',state)
marker=Path('/tmp/dag-macros-perm222-controller-author-attempts.json');attempts=json.loads(marker.read_text())if marker.exists()else[];attempts.append(str(p));save(marker,attempts)
print('PRIVATE',p,flush=True)
try:
 check(dict(path=str(PLAN),sha256='9fc88539652bb8e9a6fc9ed528e00557c3f9f48227eb475e43f56e7f427c93f9'))
 plan=json.loads(PLAN.read_text());a=plan['profiles']['actual_macro_checkpoint'];require(a['counts']==dict(custom=139,Foundation=95,artifacts=424,external=39,boundary_companion_observations=117,refresh=0),'exact scope')
 check(dict(path=str(D/'research/c222-dagperm-runtime-proposal-20261027.md'),sha256='4739ea18776bed6cb750cbcf24bfb873f3f0f8bd4a457ffa0cfa9a0abc485d1b'))
 check(dict(path=str(D/'research/c222-dagperm-runtime-plan-20261027/FILES.json'),sha256='3d80e7f755f39d1b363db06d2f45f7c89c0e8b623b44f4e7a3cf010fcc5524b7'))
 for row in json.loads((D/'research/c222-dagperm-runtime-plan-20261027/FILES.json').read_text()):check(dict(row,path=str(R/row['path'])))
 for item in plan['accepted_provider_supplements']:
  if item['module']in {m['module']for m in a['modules']}:
   check(item['root_state']);check(item['selected'])
 mods={m['module']:m for m in a['modules']};bound={e['module']:e for e in a['external']};seen=set();used=set()
 def visit(n):
  if n not in mods:require(n in bound,'unknown '+n);used.add(n);return
  if n in seen:return
  seen.add(n)
  for child in mods[n]['actual_imports']:visit(child)
 for n in a['direct_imports']:visit(n)
 require(seen==set(mods)and used==set(bound),'reachable exact closure')
 for m in a['modules']:
  check(m['source']);require(imports(m['source']['path'])==m['actual_imports'],'header '+m['module'])
  for o in m['objects']:
   check(o);dest=lib/Path(*m['module'].split('.')[:-1])/Path(o['path']).name
   dest.parent.mkdir(parents=True,exist_ok=True);require(not dest.exists(),'no provider collision');dest.symlink_to(Path(o['path']).resolve())
 for e in nested(a['external']):check(e)
 paths=[str(lib),*plan['package_paths']];require(all('/.lake/packages/'in x or x=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for x in paths[1:]),'explicit package boundary')
 providers=[]
 for n in [*mods,*bound]:
  rel=Path(*n.split('.')).with_suffix('.olean');first=next((Path(q)/rel for q in paths if(Path(q)/rel).exists()),None);require(first is not None,'missing provider '+n)
  if n in mods:expected=next(o for o in mods[n]['objects']if o['path'].endswith('.olean'))
  else:expected=bound[n]if'path'in bound[n]else bound[n]['object']
  require(rec(first)['sha256']==expected['sha256'],'first provider '+n);providers.append(dict(module=n,actual=rec(first),expected=expected))
 check(plan['compiler']);check(rec('/tmp/build-dag-macros-perm222-source.py'));check(rec(__file__))
 for name in ['ArithmeticL2Lib254','ArithmeticL2Macros254','ArithmeticL2Control254','L2Control222']:check(rec(B/(name+'.lean')))
 sources=[dict(module='BusyBeaver.ZFC.'+n,**rec(B/(n+'.lean')))for n in ['ArithmeticDagMacrosPerm222','ArithmeticDagMacrosPerm222Checks']]
 require(imports(sources[0]['path'])==['Init','BusyBeaver.ZFC.ArithmeticDagControlPerm222'],'main import')
 require(imports(sources[1]['path'])==['Init',sources[0]['module']],'checks import')
 inputs=dict(plan=rec(PLAN),profile=a,compiler=plan['compiler'],LEAN_PATH=paths,pins=list(pins.values()),actual_providers=providers,sources=sources,accepted_provider_supplements=plan['accepted_provider_supplements'])
 save(p/'inputs.json',inputs);shutil.copyfile(__file__,p/'driver.py');state.update(status='RUNNING',inputs=rec(p/'inputs.json'),counts=a['counts'],observations=observations);save(p/'AUTHOR.json',state)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for source,numreports in zip(sources,[0,22]):
  guard();check(source);snap=p/Path(source['path']).name;shutil.copyfile(source['path'],snap)
  out=lib/Path(*source['module'].split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);require(not out.exists()and not out.is_symlink(),'fresh regular target')
  log=p/(snap.stem+'.log');timing=p/(snap.stem+'.time');cmd=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),source['path']]
  start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row=dict(module=source['module'],source=source,snapshot=rec(snap),command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing));state['records'].append(row);save(p/'AUTHOR.json',state)
  require(code==0,'compile '+source['module']);require(out.is_file()and not out.is_symlink(),'regular output')
  text=log.read_text();reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
  require(not re.search(r'\b(?:error|sorryAx)\b',text),'bad diagnostics');require(len(reports)==numreports,'report count')
  for _,ax in reports:require(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'axioms')
  row.update(object=rec(out),axiom_reports=reports);save(p/'AUTHOR.json',state);check(source);guard();print('PASS',source['module'],round(row['seconds'],3),'reports',len(reports),flush=True)
 for pin in list(pins.values()):check(pin)
 state.update(status='PASS',final_observations=observations,unique_paths=len(pins),free_bytes=shutil.disk_usage('/tmp').free);save(p/'AUTHOR.json',state);print('PASS',p,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(p/'AUTHOR.json',state);raise
