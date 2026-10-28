from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
H=D/'research/c222-site215-plan-20261027'
B=D/'Lean/DiophantineConsistency'
PLAN=H/'cache-plan.json'

def rec(p):
 p=Path(p)
 return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def need(x,msg):
 if not x:raise RuntimeError(msg)
def guard():need(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
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
 need(depth==0,'balanced comments')
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(o),re.M)for n in line.split()]))
pins={};observations=0
def check(x):
 global observations
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path']);pins[a['path']]=a;observations+=1;return a

AP=D/'reviews/arithmetic-register-boxes215-final-replay.json'
check(dict(path=str(AP),sha256='c0f925175e1d7ca8144e3c5b86cc7b1935f580d190b0ff6da7f60600fa4c4bbe'))
author=json.loads(AP.read_text());need(author['status']=='PASS','final author PASS')
mf=dict(path=str(D/'reviews/arithmetic-register-boxes215-final-replay/FILES.json'),sha256='10df28e674e9d17f2a0a4c10dd7f648d3330b3647f39248a36b7810b34cc96de')
check(mf);rows=json.loads(Path(mf['path']).read_text());need(len(rows)==16,'16 final evidence files')
for x in rows:check(dict(x,path=str(R/x['path'])))
for k in ['pre_final_packet','pre_final_manifest','reauthentication','freeze','plan']:check(author[k])
oldrows=json.loads(Path(author['pre_final_manifest']['path']).read_text());need(len(oldrows)==102,'102 pre-final evidence files')
for x in oldrows:check(dict(x,path=str(R/x['path'])))
for attempt in author['attempts']:
 for row in attempt['records']:
  for k in ['snapshot','log','timing']:check(row[k])
  if 'object'in row:check(row['object'])
 for x in attempt['copies']:check(x)
for row in author['final']['records']:
 need(row['exit_code']==0,'successful final author leaf')
 for k in ['source','snapshot','object','log','timing']:check(row[k])

guard()
private=Path(tempfile.mkdtemp(prefix='register-boxes215-root-'))
lib=private/'lib';lib.mkdir()
state=dict(status='PREFLIGHT',private=str(private),driver=rec(__file__),records=[])
save(private/'ROOT.json',state)
marker=Path('/tmp/register-boxes215-root-attempts.json')
attempts=json.loads(marker.read_text())if marker.exists()else[]
attempts.append(str(private));save(marker,attempts)
print('PRIVATE',private,flush=True)
try:
 check(dict(path=str(PLAN),sha256='2db2db74059105fba7f58dacc502274b3fdb4dd0605dafa8a37bdd5bc7b35e88'))
 mf=H/'FILES.json';check(dict(path=str(mf),sha256='a2a33230abe1c069480775dded81fb10553d58de572f712e55b1334d87553fbc'))
 for x in json.loads(mf.read_text()):check(dict(x,path=str(R/x["path"])))
 plan=json.loads(PLAN.read_text())
 count=dict(custom_total=147,cached_custom=146,Foundation=95,cached_artifacts=431,boundary_primaries=41,boundary_companions=123,selected_first_artifact_providers=595,proposed_unchanged_refresh=1,proposed_new_leaves=2)
 need(plan['counts']==count,'exact scope')
 need([m['module']for m in plan['modules']if m.get('refresh')]==['BusyBeaver.ZFC.ArithmeticTapePrefix254'],'sole unchanged helper refresh')
 for x in plan['authenticated_pins']:check(x)
 mods={m['module']:m for m in plan['modules']};bound={x['module']:x for x in plan['external']}
 seen=set();active=set();used=set();order=[]
 def visit(n):
  if n not in mods:need(n in bound,'unknown '+n);used.add(n);return
  if n in seen:return
  need(n not in active,'cycle '+n);active.add(n)
  for child in mods[n]['actual_imports']:visit(child)
  active.remove(n);seen.add(n);order.append(n)
 for n in plan['direct_imports']:visit(n)
 need(seen==set(mods)and used==set(bound)and order==plan['topological_order'],'reachable DAG')
 for m in mods.values():
  check(m['source']);need(imports(m['source']['path'])==m['actual_imports'],'header '+m['module'])
  for obj in m['objects']:
   check(obj);dest=lib/Path(*m['module'].split('.')[:-1])/Path(obj['path']).name
   dest.parent.mkdir(parents=True,exist_ok=True);need(not dest.exists(),'provider collision')
   dest.symlink_to(Path(obj['path']).resolve())
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
  if 'source'in x:check(x['source'])
  for obj in [x['object'],*x['companion_observations']]:
   check(obj);rel=Path(*name.split('.')[:-1])/Path(obj['path']).name
   found=next((Path(q)/rel for q in paths if(Path(q)/rel).exists()),None)
   need(found is not None and rec(found)['sha256']==obj['sha256'],'first boundary provider '+name)
   providers.append(dict(module=name,actual=rec(found),expected=obj))
 need(len(providers)==431+41+123,'all595 artifact providers')
 check(plan['compiler']);check(rec(__file__))
 sources=[dict(module=x['module'],**rec(x['source']['path']))for x in author['final']['records']]
 need([x['module']for x in sources]==['BusyBeaver.ZFC.ArithmeticTapePrefix254','DiophantineConsistency.ArithmeticRegisterBoxes215','DiophantineConsistency.ArithmeticRegisterBoxes215Checks'],'exact fresh triple')
 need(imports(sources[0]['path'])==mods[sources[0]['module']]['actual_imports'],'prefix imports')
 need(imports(sources[1]['path'])==['Init',*plan['direct_imports']],'main imports')
 need(imports(sources[2]['path'])==['Init',sources[1]['module']],'checks imports')
 for source in sources:
  snap=private/Path(source['path']).name;shutil.copyfile(source['path'],snap);source['snapshot']=rec(snap)
 inputs=dict(plan=rec(PLAN),manifest=rec(mf),profile=plan,compiler=plan['compiler'],LEAN_PATH=paths,pins=list(pins.values()),actual_providers=providers,sources=sources)
 save(private/'inputs.json',inputs);shutil.copyfile(__file__,private/'driver.py')
 state.update(status='RUNNING',inputs=rec(private/'inputs.json'),counts=count,observations=observations);save(private/'ROOT.json',state)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for source,reports_expected in zip(sources,[0,0,14]):
  guard();check(source);check(source['snapshot'])
  out=lib/Path(*source['module'].split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  need(not out.exists()and not out.is_symlink(),'fresh regular output')
  stem=Path(source['path']).stem;log=private/(stem+'.log');timing=private/(stem+'.time')
  cmd=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),source['path']];start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row=dict(module=source['module'],source=source,snapshot=source['snapshot'],command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing));state['records'].append(row);save(private/'ROOT.json',state)
  need(code==0,'compile '+source['module']);need(out.is_file()and not out.is_symlink(),'regular output')
  txt=log.read_text();reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",txt)
  need(not re.search(r'\b(?:warning|error|sorryAx)\b',txt),'bad diagnostics');need(len(reports)==reports_expected,'report count')
  for _,ax in reports:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'axioms')
  row.update(object=rec(out),axiom_reports=reports)
  expected=next(x for x in author['final']['records'] if x['module']==row['module'])
  for k in ['source','object','log']:need(row[k]['sha256']==expected[k]['sha256'],'author matching '+k)
  need([list(x)for x in reports]==expected['axiom_reports'],'all report equality')
  row['author_object_and_full_log_equal']=True
  save(private/'ROOT.json',state);check(source);guard()
  print('PASS',source['module'],round(row['seconds'],3),'reports',len(reports),flush=True)
 for x in list(pins.values()):check(x)
 state.update(status='PASS',final_observations=observations,unique_paths=len(pins),free_bytes=shutil.disk_usage('/tmp').free)
 save(private/'ROOT.json',state);print('PASS',private,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(private/'ROOT.json',state);raise
