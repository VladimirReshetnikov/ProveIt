from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time,copy
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';B=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC';RES=D/'research'
PLAN=RES/'c222-dag-runtimeperm222-cache-plan-20261027.json';SUP=RES/'c222-dag-runtimeperm222-accepted-provider-20261027.json'
def rec(p):
 p=Path(p);p=p if p.is_absolute() else R/p
 return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def need(x,msg):
 if not x:raise RuntimeError(msg)
def guard():need(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
def nested(x):
 if isinstance(x,dict):
  if 'path'in x and'sha256'in x:yield x
  for v in x.values():yield from nested(v)
 elif isinstance(x,list):
  for v in x:yield from nested(v)
def imports(p):
 s=Path(p).read_text();o=[];i=depth=0
 while i<len(s):
  pair=s[i:i+2]
  if depth:
   if pair=='/-':depth+=1;i+=2
   elif pair=='-/':depth-=1;i+=2
   else:o.append('\n'if s[i]=='\n'else' ');i+=1
  elif pair=='/-':depth=1;i+=2
  elif pair=='--':
   while i<len(s)and s[i]!='\n':i+=1
  else:o.append(s[i]);i+=1
 need(depth==0,'balanced source comments')
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(o),re.M)for n in line.split()]))
pins={};observations=0
def check(x):
 global observations
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path']);pins[a['path']]=a;observations+=1;return a
guard();private=Path(tempfile.mkdtemp(prefix='dag-runtimeperm222-root-'));lib=private/'lib';lib.mkdir()
state=dict(status='PREFLIGHT',private=str(private),driver=rec(__file__),records=[]);save(private/'AUTHOR.json',state)
marker=Path('/tmp/dag-runtimeperm222-root-attempts.json');attempts=json.loads(marker.read_text())if marker.exists()else[];attempts.append(str(private));save(marker,attempts)
print('PRIVATE',private,flush=True)
try:
 AP=D/'reviews/arithmetic-dag-runtimeperm222-replay.json'
 check(dict(path=str(AP),sha256='0a214c73daa754812658979554a9dd163400519c258dbf3400a504095cde1135'))
 author=json.loads(AP.read_text());need(author['status']=='PASS'and author['final']['status']=='PASS','author final state')
 check(author['evidence_manifest']);mf=json.loads(Path(author['evidence_manifest']['path']).read_text())
 for x in mf:check(x)
 expected_records={x['module']:x for x in author['final']['records']}
 check(dict(path=str(PLAN),sha256='e0d0736f57ebddca9a2530f93fdec69308ed77c1dec74c18787866f2ebfaf3d6'))
 check(dict(path=str(SUP),sha256='a5c0d5a944a2b379db14adb0a922e479644d2bab30cdb590f375053d6f47644e'))
 plan=json.loads(PLAN.read_text());sup=json.loads(SUP.read_text())
 count=dict(closure_custom=152,cached_custom=151,Foundation=95,cached_artifacts=436,external=39,boundary_companion_observations=117,proposed_refresh=1,new_leaves=2)
 need(plan['counts']==count and sup['counts']==count,'exact scope')
 for name,sha in [('c222-dag-runtimeperm222-plan-20261027','7e90f8e9f9853f699cdb6fb6a039db271e0cdbf6be0229fc6eb256bedc0e8613'),('c222-dag-runtimeperm222-accepted-provider-20261027','0ce6495cf5982f054d2f21b012623ee35400bcce85cf9ec33a9e3e4c14c7878f')]:
  mf=RES/name/'FILES.json';check(dict(path=str(mf),sha256=sha))
  for x in json.loads(mf.read_text()):check(x)
 for x in plan['authenticated_paths']:check(x)
 # The frozen supplement records first prepared source bytes. Later routine proof
 # edits are independently captured below; prerequisite pins remain mandatory.
 prepared={x['path']for x in sup['new_sources']}
 for x in sup['authentication']:
  if x['path']not in prepared:check(x)
 for x in nested(sup['provider_override']):check(x)
 for key in ['root_acceptance','root_manifest','root_state','peer_packet','peer_manifest']:check(sup[key])
 for key in ['root_manifest','peer_manifest']:
  for x in json.loads(Path(sup[key]['path']).read_text()):check(x)
 mods={m['module']:copy.deepcopy(m)for m in plan['modules']};override=sup['provider_override']
 mods[override['module']]['objects']=[override['accepted_provider']]
 refresh='BusyBeaver.ZFC.ArithmeticPositiveSimulation254';need(mods[refresh]['objects']==[],'old generic object excluded')
 need(mods[refresh]['source']['sha256']=='ec9c249013345061fb2dd99b1cb387f10dfd5d69447100465ff2b7558e949290','unchanged generic')
 bound={x['module']:x for x in plan['external']};seen=set();active=set();used=set();order=[]
 def visit(n):
  if n not in mods:need(n in bound,'unknown '+n);used.add(n);return
  if n in seen:return
  need(n not in active,'cycle '+n);active.add(n)
  for child in mods[n]['actual_imports']:visit(child)
  active.remove(n);seen.add(n);order.append(n)
 for n in plan['direct_imports']:visit(n)
 need(seen==set(mods)and used==set(bound),'exact reachable closure')
 need(order==plan['topological_order'],'topological order unchanged')
 for m in mods.values():
  check(m['source']);need(imports(m['source']['path'])==m['actual_imports'],'header '+m['module'])
  for obj in m['objects']:
   check(obj);dest=lib/Path(*m['module'].split('.')[:-1])/Path(obj['path']).name
   dest.parent.mkdir(parents=True,exist_ok=True);need(not dest.exists(),'provider collision');dest.symlink_to(Path(obj['path']).resolve())
 for x in nested(plan['external']):check(x)
 paths=[str(lib),*plan['package_paths']]
 need(all('/.lake/packages/'in x or x=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for x in paths[1:]),'package-only external path')
 providers=[]
 for name,m in mods.items():
  for obj in m['objects']:
   rel=Path(*name.split('.')[:-1])/Path(obj['path']).name
   found=next((Path(q)/rel for q in paths if(Path(q)/rel).exists()),None)
   need(found is not None and rec(found)['sha256']==obj['sha256'],'first custom provider '+name)
   providers.append(dict(module=name,actual=rec(found),expected=obj))
 for name,x in bound.items():
  primary=x if'path'in x else x['object'];allobjs=[primary,*x['companion_observations']]
  for obj in allobjs:
   rel=Path(*name.split('.')[:-1])/Path(obj['path']).name
   found=next((Path(q)/rel for q in paths if(Path(q)/rel).exists()),None)
   need(found is not None and rec(found)['sha256']==obj['sha256'],'first boundary provider '+name)
   providers.append(dict(module=name,actual=rec(found),expected=obj))
 need(len(providers)==436+39+117,'all artifact providers')
 check(plan['compiler']);check(rec(__file__))
 names=['ArithmeticPositiveSimulation254','ArithmeticDagRuntimePerm222','ArithmeticDagRuntimePerm222Checks']
 sources=[dict(module='BusyBeaver.ZFC.'+n,**rec(B/(n+'.lean')))for n in names]
 need(imports(sources[0]['path'])==mods[refresh]['actual_imports'],'generic import')
 need(imports(sources[1]['path'])==['Init',*plan['direct_imports']],'main import')
 need(imports(sources[2]['path'])==['Init',sources[1]['module']],'checks import')
 for source in sources:
  need(source['sha256']==expected_records[source['module']]['source']['sha256'],'frozen final source')
  snap=private/Path(source['path']).name;shutil.copyfile(source['path'],snap);source['snapshot']=rec(snap)
 inputs=dict(plan=rec(PLAN),supplement=rec(SUP),profile=dict(counts=count,modules=list(mods.values()),external=plan['external'],topological_order=order),compiler=plan['compiler'],LEAN_PATH=paths,pins=list(pins.values()),actual_providers=providers,sources=sources,prepared_sources=sup['new_sources'],historical_generic_excluded=True)
 save(private/'inputs.json',inputs);shutil.copyfile(__file__,private/'driver.py');state.update(status='RUNNING',inputs=rec(private/'inputs.json'),counts=count,observations=observations);save(private/'AUTHOR.json',state)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for source,reports_expected in zip(sources,[0,0,11]):
  guard();check(source);check(source['snapshot'])
  out=lib/Path(*source['module'].split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);need(not out.exists()and not out.is_symlink(),'fresh regular output')
  stem=Path(source['path']).stem;log=private/(stem+'.log');timing=private/(stem+'.time')
  cmd=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),source['path']];start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row=dict(module=source['module'],source=source,snapshot=source['snapshot'],command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing));state['records'].append(row);save(private/'AUTHOR.json',state)
  need(code==0,'compile '+source['module']);need(out.is_file()and not out.is_symlink(),'regular output')
  txt=log.read_text();reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",txt)
  need(not re.search(r'\b(?:warning|error|sorryAx)\b',txt),'bad diagnostics');need(len(reports)==reports_expected,'report count')
  for _,ax in reports:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'axioms')
  row.update(object=rec(out),axiom_reports=reports)
  expected=expected_records[source['module']]
  need(row['object']['sha256']==expected['object']['sha256'],'author object equality')
  need(row['log']['sha256']==expected['log']['sha256'],'author complete log equality')
  need([list(x)for x in reports]==expected['axiom_reports'],'all author reports')
  row['author_object_and_full_log_equal']=True
  save(private/'AUTHOR.json',state);check(source);guard();print('PASS',source['module'],round(row['seconds'],3),'reports',len(reports),flush=True)
 for x in list(pins.values()):check(x)
 state.update(status='PASS',final_observations=observations,unique_paths=len(pins),free_bytes=shutil.disk_usage('/tmp').free);save(private/'AUTHOR.json',state);print('PASS',private,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(private/'AUTHOR.json',state);raise
