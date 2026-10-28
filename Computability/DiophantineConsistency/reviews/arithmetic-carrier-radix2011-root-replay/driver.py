from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
PLAN=D/'research/arithmetic-carrier-radix2011-cache-plan.json'
SCOPE=D/'research/arithmetic-carrier-radix2011-proposal.md'
pins={}
def need(ok,message):
 if not ok:raise RuntimeError(message)
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path'])
 if 'bytes'in x:need(a['bytes']==x['bytes'],'size '+x['path'])
 pins[a['path']]=a;return a
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def guard():need(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
def imports(p):
 s=Path(p).read_text();out=[];i=depth=0
 while i<len(s):
  q=s[i:i+2]
  if depth:
   if q=='/-':depth+=1;i+=2
   elif q=='-/':depth-=1;i+=2
   else:out.append('\n'if s[i]=='\n'else' ');i+=1
  elif q=='/-':depth=1;i+=2
  elif q=='--':
   while i<len(s)and s[i]!='\n':i+=1
  else:out.append(s[i]);i+=1
 need(not depth,'balanced comments');t=''.join(out)
 return list(dict.fromkeys(['Init']+[n for line in re.findall(
  r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',t,re.M)for n in line.split()]))
guard();P=Path(tempfile.mkdtemp(prefix='arithmetic-carrier-radix2011-root-'))
lib=P/'lib';lib.mkdir();logs=P/'logs';logs.mkdir()
shutil.copyfile(__file__,P/'driver.py')
state=dict(status='PREFLIGHT',private=str(P),driver=rec(P/'driver.py'),records=[])
save(P/'ROOT.json',state)
marker=Path('/tmp/arithmetic-carrier-radix2011-root-runs.json')
runs=json.loads(marker.read_text())if marker.exists()else[]
runs.append(str(P));save(marker,runs);print('PRIVATE',P,flush=True)
try:
 ap=check(dict(path=str(D/'reviews/arithmetic-carrier-radix2011-replay.json'),sha256='7d7a31e4294050e174716124e580b0ce4b535df31a91ea47ed443a6d3d7560b5'))
 check(dict(path=str(D/'reviews/arithmetic-carrier-radix2011-author.md'),sha256='75fda9b5eceae39e8bb58dff0add62a135969a7a1141f0799f9db4da71d3b29e'))
 author=json.loads(Path(ap['path']).read_text());need(author['status']=='PASS'and len(author['attempts'])==1,'one author attempt')
 check(author['manifest']);need(author['manifest']['sha256']=='d9cc6580c61974703d491d17e30ba8e48b05a77a2c8358f9d5393bdda768d5b5','author manifest pin')
 ar=json.loads(Path(author['manifest']['path']).read_text());need(len(ar)==14,'all14 author files')
 for z in ar:check(z)
 for k in ['freeze_driver','inputs','providers','state','durable_state','plan','proposal','driver','freeze_authentication']:check(author[k])
 fa=json.loads(Path(author['freeze_authentication']['path']).read_text());need(fa['status']=='PASS','frozen author evidence')
 for z in fa['pins']:check(z)
 for at in author['attempts']:
  check(at['state']);ast=json.loads(Path(at['state']['path']).read_text());need(ast['status']=='PASS','terminal author')
  check(ast['inputs']);check(ast['driver'])
  for row in ast['records']:
   need(row['source']['sha256']==row['snapshot']['sha256'],'history source snapshot')
   need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'history caps')
   for k in ['snapshot','log','timing','object']:check(row[k])
 for row in author['records']:
  need(row['exit_code']==0,'final author status')
  for k in ['source','snapshot','log','timing','object']:check(row[k])
 check(dict(path=str(PLAN),sha256='ac2fa36f63fd5ce826656a9096f7b3241a086a362ec1c41850555fb6a142c32e'))
 check(dict(path=str(SCOPE),sha256='f5c9d96e23ea9d7ba702af7ac9624b039b047f05557e557c221d79d68065745d'));plan=json.loads(PLAN.read_text())
 expected=dict(custom=138,Foundation=95,artifacts=423,external=50,boundary_primaries=50,boundary_companions=100,boundary_artifacts=150,actual_first_providers=573,fresh_prerequisites=0)
 need(plan['counts']==expected,'exact prerequisite scope')
 for z in plan['pins']:check(z)
 mf=D/'research/arithmetic-carrier-radix2011-plan-evidence/FILES.json'
 check(dict(path=str(mf),sha256='61297390c85d67b2a609ef97252eef4165fec45cd978f1f5780bf913cf60cb6e'))
 rows=json.loads(mf.read_text());need(len(rows)==9,'complete frozen plan')
 for z in rows:check(z)
 check(dict(path=str(D/'reviews/arithmetic-carrier-radix2011-plan-root.json'),sha256='4d68f16c65901adcaee6fdf94257b09454d59cdfea51ff2d27555e0ea464efda'))
 check(dict(path=str(D/'reviews/arithmetic-carrier-radix2011-plan-root.md'),sha256='3f4e9db7a22155ebe49f2a2c159feb236cc231c4f44414233a0ca90d8f57709a'))
 mods={z['module']:z for z in plan['modules']};ext={z['module']:z for z in plan['external']}
 seen=set();active=set();used=set();order=[]
 def visit(n):
  if n not in mods:need(n in ext,'unknown boundary '+n);used.add(n);return
  if n in seen:return
  need(n not in active,'cycle');active.add(n);m=mods[n];check(m['source'])
  need(imports(m['source']['path'])==m['imports'],'header '+n)
  for dep in m['imports']:visit(dep)
  active.remove(n);seen.add(n);order.append(n)
 for n in plan['direct_imports']:visit(n)
 need(seen==set(mods)and used==set(ext)and order==plan['topological_order'],'exact DAG')
 for n in order:
  for z in mods[n]['objects']:
   check(z);dest=lib/Path(*n.split('.')[:-1])/Path(z['path']).name
   dest.parent.mkdir(parents=True,exist_ok=True);need(not dest.exists(),'collision')
   dest.symlink_to(Path(z['path']).resolve())
 paths=[str(lib),*plan['boundary_search']]
 need(all('/.lake/packages/'in p or p=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for p in paths[1:]),'package-only fallback')
 providers=[]
 for m in list(mods.values())+list(ext.values()):
  if isinstance(m.get('source'),dict):check(m['source'])
  for z in m.get('objects',m.get('artifacts',[])):
   check(z);rel=Path(*m['module'].split('.')[:-1])/Path(z['path']).name
   first=next((Path(a)/rel for a in paths if(Path(a)/rel).is_file()),None)
   need(first is not None,'missing first provider')
   providers.append(dict(module=m['module'],expected=z,actual=check(dict(z,path=str(first)))))
 need(len(providers)==573,'all573 providers');check(plan['compiler'])
 sources=[dict(module='DiophantineConsistency.'+n,**check(rec(D/('Lean/DiophantineConsistency/'+n+'.lean'))))
  for n in ['ArithmeticCarrierRadix2011','ArithmeticCarrierRadix2011Checks']]
 need(imports(sources[0]['path'])==['Init',*plan['direct_imports']],'main imports')
 need(imports(sources[1]['path'])==['Init',sources[0]['module']],'checks imports')
 for source in sources:
  expected_source=next(r for r in author['records']if r['module']==source['module'])['source']
  need(source['sha256']==expected_source['sha256'],'final source pin')
  snap=logs/Path(source['path']).name;shutil.copyfile(source['path'],snap);source['snapshot']=rec(snap)
 save(P/'providers.json',providers);save(P/'authentication.json',dict(pins=list(pins.values())))
 inputs=dict(profile_reference=rec(PLAN),scope=rec(SCOPE),counts=expected,sources=sources,
  providers=rec(P/'providers.json'),authentication=rec(P/'authentication.json'),compiler=plan['compiler'],LEAN_PATH=paths)
 save(P/'inputs.json',inputs);state.update(status='RUNNING',inputs=rec(P/'inputs.json'));save(P/'ROOT.json',state)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for source,wanted in zip(sources,[0,8]):
  guard();check(source);check(source['snapshot'])
  output=lib/Path(*source['module'].split('.')).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
  need(not output.exists()and not output.is_symlink(),'fresh regular output')
  stem=Path(source['path']).stem;log=logs/(stem+'.log');timing=logs/(stem+'.time')
  cmd=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(output),source['path']]
  start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row=dict(module=source['module'],source=source,snapshot=source['snapshot'],command=cmd,exit_code=code,
   seconds=time.monotonic()-start,log=rec(log),timing=rec(timing));state['records'].append(row)
  if output.is_file():row['object']=rec(output)
  save(P/'ROOT.json',state);print(log.read_text(),flush=True);need(code==0,'compiler '+source['module'])
  text=log.read_text();need(not re.search(r'\b(?:warning|error|sorryAx)\b',text),'clean diagnostics')
  reports=[list(z)for z in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
  need(len(reports)==wanted,'all reports')
  for _,ax in reports:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
  need(output.is_file()and not output.is_symlink(),'regular object');row['axiom_reports']=reports
  expected_row=next(r for r in author['records']if r['module']==row['module'])
  for k in ['source','object','log']:need(row[k]['sha256']==expected_row[k]['sha256'],'author equality '+k)
  need(reports==expected_row['axiom_reports'],'identical reports');row['author_object_and_full_log_equal']=True
  save(P/'ROOT.json',state);check(source);guard();print('PASS',source['module'],round(row['seconds'],3),flush=True)
 for z in list(pins.values()):check(z)
 state.update(status='PASS',observed_paths=len(pins),free_bytes=shutil.disk_usage('/tmp').free)
 save(P/'ROOT.json',state);print('PASS',P,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(P/'ROOT.json',state);raise
