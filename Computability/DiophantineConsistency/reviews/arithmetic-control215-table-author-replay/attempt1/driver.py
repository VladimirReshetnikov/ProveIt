from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time,copy
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';REV=D/'reviews'
PLAN=D/'research/c222-dagperm-p215-bisim-cache-plan-20261026.json'
ROOTSTATE=REV/'arithmetic-dag-controlperm222-root-replay/ROOT.json'
ROOTMAN=ROOTSTATE.parent/'FILES.json'
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,j):Path(p).write_text(json.dumps(j,indent=2)+'\n')
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def guard():require(shutil.disk_usage('/tmp').free>=512*1024**2,'512 MiB reserve')
pins={};observations=0
def check(r):
 global observations
 a=rec(r['path']);require(a['sha256']==r['sha256'],'hash '+r['path']);pins[a['path']]=a;observations+=1;return a
def nested(x):
 if isinstance(x,dict):
  if 'path'in x and 'sha256'in x:yield x
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
 require(depth==0,'comments')
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M)for n in line.split()]))
guard();p=Path(tempfile.mkdtemp(prefix='control215-table-controller-author-'));lib=p/'lib';lib.mkdir()
state={'status':'PREFLIGHT','private':str(p),'driver':rec(__file__),'records':[]};save(p/'AUTHOR.json',state)
marker=Path('/tmp/control215-table-controller-author-attempts.json')
attempts=json.loads(marker.read_text())if marker.exists()else[];attempts.append(str(p));save(marker,attempts)
print('PRIVATE',p,flush=True)
try:
 check(dict(path=str(PLAN),sha256='2ad54bece693f305077d6f8c35fb5a6b8aec9769eb346cecba52bcd682f7883f'))
 check(dict(path=str(ROOTSTATE),sha256='f3228324a345d488692b682ed23b44cff2ef6e017dddb52101db535dc84092eb'))
 check(dict(path=str(ROOTMAN),sha256='3e9274806a638ed6d189bada8877bea7ecabb7f889aba03b636ab39b83673614'))
 for row in json.loads(ROOTMAN.read_text()):
  q=Path(row['path']);check(dict(row,path=str(q if q.is_absolute()else ROOTMAN.parent/q)))
 a=json.loads(PLAN.read_text());root=json.loads(ROOTSTATE.read_text());require(root['status']=='PASS','root status')
 for r in a['pins']:check(r)
 for path in [D/'research/c222-dagperm-p215-bisim-proposal-20261026.md',D/'research/c222-dagperm-p215-bisim-plan/FILES.json',
              REV/'arithmetic-dag-controlperm222-root.md',Path('/tmp/build-control215-table-source.py'),Path('/tmp/control215-table-source-audit.json'),Path(__file__)]:check(rec(path))
 mods={r['module']:copy.deepcopy(r)for r in a['modules']};changes=[]
 for r in root['records']:
  for key in ['source','snapshot','object','log','timing']:check(r[key])
  if r['module']not in mods:continue
  old=mods[r['module']];require(r['source']['sha256']==old['source']['sha256'],'root source')
  require(r['object']['sha256']==old['objects'][0]['sha256'],'byte-identical root object')
  changes.append({'module':r['module'],'historical_objects':old['objects'],'accepted_object':r['object']})
  old['objects']=[r['object']]
 require(len(changes)==2,'exact root supplement')
 for r in mods.values():
  check(r['source']);require(imports(r['source']['path'])==r['actual_imports'],'header '+r['module'])
  for obj in r['objects']:check(obj)
 for e in nested(a['external']):check(e)
 require(a['counts']==dict(custom=140,Foundation=95,artifacts=425,external=39,fresh_prerequisites=0),'scope')
 seen=set();used=set();edge={r['module']for r in a['external']}
 def visit(n):
  if n not in mods:require(n in edge,'unknown import '+n);used.add(n);return
  if n in seen:return
  seen.add(n)
  for k in mods[n]['actual_imports']:visit(k)
 for n in a['direct_imports']:visit(n)
 require(seen==set(mods)and used==edge,'exact reachable DAG')
 for n,r in mods.items():
  for obj in r['objects']:
   dest=lib/Path(*n.split('.')[:-1])/Path(obj['path']).name
   dest.parent.mkdir(parents=True,exist_ok=True);require(not dest.exists(),'duplicate artifact')
   dest.symlink_to(Path(obj['path']).resolve())
 paths=[str(lib),*root['LEAN_PATH'][1:]]
 require(all('/.lake/packages/'in x or x=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for x in paths[1:]),'package boundary')
 providers=[]
 for n in list(mods)+[e['module']for e in a['external']]:
  rel=Path(*n.split('.')).with_suffix('.olean');first=next((Path(q)/rel for q in paths if(Path(q)/rel).exists()),None)
  require(first is not None,'missing provider '+n)
  if n in mods:expected=next(o for o in mods[n]['objects']if o['path'].endswith('.olean'))
  else:
   e=next(e for e in a['external']if e['module']==n);expected=e if'path'in e else e['object']
  actual=rec(first);require(actual['sha256']==expected['sha256'],'actual provider '+n)
  providers.append({'module':n,'actual':actual,'expected':expected})
 check(a['compiler'])
 new=['BusyBeaver.ZFC.ArithmeticControl215Table','BusyBeaver.ZFC.ArithmeticControl215TableChecks']
 sources=[dict(module=n,**rec(R/'Computability/BusyBeaver/Lean'/Path(*n.split('.')).with_suffix('.lean')))for n in new]
 require(imports(sources[0]['path'])==['Init',*a['direct_imports']],'new imports')
 require(imports(sources[1]['path'])==['Init',new[0]],'Checks imports')
 inputs={'cache':rec(PLAN),'modules':list(mods.values()),'external':a['external'],'pins':list(pins.values()),'compiler':a['compiler'],
 'LEAN_PATH':paths,'actual_providers':providers,'sources':sources,'counts':a['counts'],
 'provider_supplement':{'root_commit':'c604775130','root_state':rec(ROOTSTATE),'root_manifest':rec(ROOTMAN),'changes':changes,
 'scope':'Select the two accepted byte-identical root objects without modifying the frozen historical pending plan.'}}
 save(p/'inputs.json',inputs);shutil.copyfile(__file__,p/'driver.py')
 state.update(status='RUNNING',inputs=rec(p/'inputs.json'),counts=a['counts'],preflight_observations=observations);save(p/'AUTHOR.json',state)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for source,numreports in zip(sources,[0,9]):
  guard();check(source);n=source['module'];snap=p/Path(source['path']).name;shutil.copyfile(source['path'],snap)
  out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  require(not out.exists()and not out.is_symlink(),'fresh target')
  log=p/(snap.stem+'.log');timing=p/(snap.stem+'.time');cmd=[a['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),source['path']]
  start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'module':n,'source':source,'snapshot':rec(snap),'command':cmd,'exit_code':code,'seconds':time.monotonic()-start,'log':rec(log),'timing':rec(timing)}
  state['records'].append(row);save(p/'AUTHOR.json',state)
  require(code==0,'compile '+n);require(out.is_file()and not out.is_symlink(),'regular output')
  text=log.read_text();reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
  require(not re.search(r'\b(?:warning|error|sorryAx)\b',text),'diagnostics')
  require(len(reports)==numreports,'report count')
  for _,ax in reports:require(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'axioms')
  row.update(object=rec(out),axiom_reports=reports);check(source);guard();save(p/'AUTHOR.json',state)
  print('PASS',n,round(row['seconds'],3),'reports',len(reports),flush=True)
 for pin in list(pins.values()):check(pin)
 state.update(status='PASS',final_observations=observations,unique_paths=len(pins),free_bytes=shutil.disk_usage('/tmp').free)
 save(p/'AUTHOR.json',state);print('PASS',p,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(p/'AUTHOR.json',state);raise
