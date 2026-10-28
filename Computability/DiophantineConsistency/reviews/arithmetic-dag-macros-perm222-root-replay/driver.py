from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
OBS={}
def need(x,m):
 if not x:raise RuntimeError(m)
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def check(x):
 p=Path(x['path']);p=p if p.is_absolute() else R/p;a=rec(p)
 need(a['sha256']==x['sha256'],'hash '+str(p))
 if 'bytes'in x:need(a['bytes']==x['bytes'],'size '+str(p))
 OBS[a['path']]=a;return a
def nested(x):
 if isinstance(x,dict):
  if 'path'in x and 'sha256'in x:yield x
  for v in x.values():yield from nested(v)
 elif isinstance(x,list):
  for v in x:yield from nested(v)
def load(p):return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def imports(p):
 s=Path(p).read_text();out=[];i=depth=0
 while i<len(s):
  pair=s[i:i+2]
  if depth:
   if pair=='/-':depth+=1;i+=2
   elif pair=='-/':depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif pair=='/-':depth=1;i+=2
  elif pair=='--':
   while i<len(s) and s[i]!='\n':i+=1
  else:out.append(s[i]);i+=1
 need(depth==0,'comments');s=''.join(out);names=[] if re.search(r'^\s*prelude\s*$',s,re.M) else ['Init']
 for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M):names.extend(line.split())
 return list(dict.fromkeys(names))
def guard():need(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
guard();p=Path(tempfile.mkdtemp(prefix='arithmetic-dag-macros-perm222-root-'));lib=p/'lib';lib.mkdir();shutil.copyfile(__file__,p/'driver.py')
s=dict(status='PREFLIGHT',private=str(p),records=[]);save(p/'ROOT.json',s);Path('/tmp/arithmetic-dag-macros-perm222-root-latest').write_text(str(p)+'\n');print('PRIVATE',p,flush=True)
attempts_path=Path('/tmp/arithmetic-dag-macros-perm222-root-attempts.json')
previous=load(attempts_path) if attempts_path.exists() else []
previous.append(str(p));save(attempts_path,previous)
try:
 for name,h in [('arithmetic-dag-macros-perm222-author.md','3a69da0ef077349d6ab82d493bd2da66a0a9d6bae38e1f43d5c54cdecbb00832'),('arithmetic-dag-macros-perm222-replay.json','0cf62d5a3d713c31e422929ee60f3e8a4c7fec8e633185ddea059af5f58315ea'),('arithmetic-dag-macros-perm222-author-replay/FILES.json','99d4a2cfe83b16eb49315950272833ab32e3bbaf3eb6c5810cc4f3190a56845f')]:check(dict(path=str(V/name),sha256=h))
 a=load(V/'arithmetic-dag-macros-perm222-replay.json');need(a['status']==a['final']['status']=='PASS','author PASS')
 manifest=load(V/'arithmetic-dag-macros-perm222-author-replay/FILES.json');need(len(manifest)==24,'author24files')
 for x in manifest:check(x)
 for key in a:
  if key!='attempts':
   for x in nested(a[key]):check(x)
 d=load(a['inputs']['path']);plan=load(d['plan']['path']);profile=d['profile']
 need(profile==plan['profiles']['actual_macro_checkpoint'],'exact immutable profile')
 need(d['accepted_provider_supplements']==plan['accepted_provider_supplements'],'explicit supplements')
 counts=dict(custom=139,Foundation=95,artifacts=424,external=39,boundary_companion_observations=117,refresh=0)
 need(profile['counts']==a['counts']==counts,'exact counts')
 for x in d['pins']:check(x)
 for x in nested(profile):check(x)
 for x in nested(d['accepted_provider_supplements']):check(x)
 for x in load(R/'Computability/DiophantineConsistency/research/c222-dagperm-runtime-plan-20261027/FILES.json'):check(x)
 mods={m['module']:m for m in profile['modules']};edge={e['module']:e for e in profile['external']}
 need(len(mods)==139 and sum(n.startswith('Foundation.') for n in mods)==95,'modules')
 need(sum(len(m['objects']) for m in mods.values())==424 and len(edge)==39,'artifacts')
 seen=set();active=set();used=set()
 def visit(n):
  if n not in mods:need(n in edge,'unknown boundary '+n);used.add(n);return
  if n in seen:return
  need(n not in active,'cycle');active.add(n)
  row=mods[n];need(imports(row['source']['path'])==row['actual_imports'],'source header '+n)
  for dep in row['actual_imports']:visit(dep)
  active.remove(n);seen.add(n)
 for n in profile['direct_imports']:visit(n)
 need(seen==set(mods) and used==set(edge),'exact reachable DAG')
 for attempt in a['attempts']:
  check(attempt['durable']);historical=attempt['state']
  need(load(attempt['durable']['path'])==historical,'historical state identity')
  folder=Path(attempt['durable']['path']).parent
  check(dict(historical['driver'],path=str(folder/'driver.py')))
  check(historical['inputs'])
  for row in historical['records']:
   need(row['source']['sha256']==row['snapshot']['sha256'],'historical source snapshot')
   for key in ['snapshot','log','timing','object']:
    if key in row:check(row[key])
 old=a['final']['records'];need(len(old)==2,'exact two leaves')
 for row in old:
  need(row['exit_code']==0,'author result')
  for k in ['source','snapshot','object','log','timing']:check(row[k])
 need(imports(old[0]['source']['path'])==['Init',*profile['direct_imports']],'new main import')
 need(imports(old[1]['source']['path'])==['Init',old[0]['module']],'new Checks import')
 need(all(row['module'] not in mods for row in old),'new targets excluded')
 for n,row in mods.items():
  for obj in row['objects']:
   dest=lib/Path(*n.split('.')[:-1])/Path(obj['path']).name;dest.parent.mkdir(parents=True,exist_ok=True)
   need(not dest.exists(),'fresh cached link');dest.symlink_to(Path(obj['path']).resolve())
 paths=[str(lib),*plan['package_paths']]
 need(all('/.lake/packages/' in x or x=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean' for x in paths[1:]),'package-only boundary')
 providers=[]
 for n,row in [*mods.items(),*edge.items()]:
  artifacts=row['objects'] if n in mods else [row if 'path'in row else row['object'],*row['companion_observations']]
  for obj in artifacts:
   rel=Path(*n.split('.')[:-1])/Path(obj['path']).name;first=next((Path(q)/rel for q in paths if(Path(q)/rel).is_file()),None)
   need(first is not None,'first provider absent '+n);actual=check(dict(obj,path=str(first)))
   providers.append(dict(module=n,actual=actual,expected=obj))
 check(d['compiler']);guard()
 save(p/'inputs.json',d);save(p/'providers.json',providers);shutil.copyfile(V/'arithmetic-dag-macros-perm222-replay.json',p/'author-packet.json')
 s.update(status='RUNNING',counts=counts,LEAN_PATH=paths,inputs=rec(p/'inputs.json'),providers=rec(p/'providers.json'));save(p/'ROOT.json',s)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for author in old:
  guard();source=author['source'];check(source)
  n=author['module'];snap=p/Path(source['path']).name;shutil.copyfile(source['path'],snap)
  out=lib/(n.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True);need(not out.exists() and not out.is_symlink(),'fresh regular output')
  log=p/(snap.stem+'.log');timing=p/(snap.stem+'.time');command=[d['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),source['path']]
  print('START',n,flush=True);start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row=dict(module=n,source=source,snapshot=rec(snap),command=command,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing));s['records'].append(row);save(p/'ROOT.json',s)
  need(code==0,'compile '+n);need(out.is_file() and not out.is_symlink(),'regular output')
  text=log.read_text();need(not re.search(r'\b(warning|error|sorryAx)\b',text),'diagnostics')
  reports=[list(x) for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
  need(reports==author['axiom_reports'],'complete reports')
  for _,axs in reports:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',axs))<={'propext','Classical.choice','Quot.sound'},'axioms')
  need(rec(out)['sha256']==author['object']['sha256'] and rec(log)['sha256']==author['log']['sha256'],'object/full-log equality')
  row.update(object=rec(out),axiom_reports=reports,matches_author=True);check(source)
  for x in list(OBS.values()):check(x)
  save(p/'ROOT.json',s);print('PASS',n,round(row['seconds'],3),flush=True)
 guard();s.update(status='PASS',observations=len(OBS),provider_artifacts=len(providers),free_bytes=shutil.disk_usage('/tmp').free);save(p/'pins.json',list(OBS.values()));save(p/'ROOT.json',s);print('PASS',p,flush=True)
except BaseException as e:
 s.update(status='FAILED',failure=str(e));save(p/'pins.json',list(OBS.values()));save(p/'ROOT.json',s);raise
