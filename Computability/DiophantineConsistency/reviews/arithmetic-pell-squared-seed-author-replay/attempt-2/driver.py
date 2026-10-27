from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
PLAN=D/'research/arithmetic-pell-squared-seed-cache-plan.json'
SCOPE=D/'research/arithmetic-pell-squared-seed-proposal.md'
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
guard();P=Path(tempfile.mkdtemp(prefix='arithmetic-pell-squared-seed-author-'))
lib=P/'lib';lib.mkdir();logs=P/'logs';logs.mkdir()
shutil.copyfile(__file__,P/'driver.py')
state=dict(status='PREFLIGHT',private=str(P),driver=rec(P/'driver.py'),records=[])
save(P/'state.json',state)
marker=Path('/tmp/arithmetic-pell-squared-seed-author-runs.json')
runs=json.loads(marker.read_text())if marker.exists()else[]
runs.append(str(P));save(marker,runs);print('PRIVATE',P,flush=True)
try:
 check(dict(path=str(PLAN),sha256='bc4e5d0235e3948bfac8deee9c864df2ae98c98672ac530316076da40df44be1'))
 check(rec(SCOPE));plan=json.loads(PLAN.read_text())
 expected=dict(custom=99,Foundation=95,artifacts=384,external=38,boundary_artifacts=114,actual_first_providers=498,fresh_prerequisites=0)
 need(plan['counts']==expected,'exact prerequisite scope')
 for z in plan['pins']:check(z)
 mf=D/'research/arithmetic-pell-squared-seed-plan-FILES.json'
 check(dict(path=str(mf),sha256='a84157fd3b381805ecfc8a29e208a59c18b426b5e87d57dc256c5a6b23ecd589'))
 rows=json.loads(mf.read_text());rows=rows['files']if isinstance(rows,dict)else rows
 for z in rows:
  q=Path(z['path']);base=R if q.parts[0]in ['Logic','Computability']else mf.parent
  check(dict(z,path=str(base/q)))
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
 need(len(providers)==498,'all498 providers');check(plan['compiler'])
 sources=[dict(module='DiophantineConsistency.'+n,**check(rec(D/('Lean/DiophantineConsistency/'+n+'.lean'))))
  for n in ['ArithmeticPellSquaredSeed','ArithmeticPellSquaredSeedChecks']]
 need(imports(sources[0]['path'])==['Init',*plan['direct_imports']],'main imports')
 need(imports(sources[1]['path'])==['Init',sources[0]['module']],'checks imports')
 for source in sources:
  snap=logs/Path(source['path']).name;shutil.copyfile(source['path'],snap);source['snapshot']=rec(snap)
 save(P/'providers.json',providers);save(P/'authentication.json',dict(pins=list(pins.values())))
 inputs=dict(profile_reference=rec(PLAN),scope=rec(SCOPE),counts=expected,sources=sources,
  providers=rec(P/'providers.json'),authentication=rec(P/'authentication.json'),compiler=plan['compiler'],LEAN_PATH=paths)
 save(P/'inputs.json',inputs);state.update(status='RUNNING',inputs=rec(P/'inputs.json'));save(P/'state.json',state)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for source,wanted in zip(sources,[0,4]):
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
  save(P/'state.json',state);print(log.read_text(),flush=True);need(code==0,'compiler '+source['module'])
  text=log.read_text();need(not re.search(r'\b(?:warning|error|sorryAx)\b',text),'clean diagnostics')
  reports=[list(z)for z in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
  need(len(reports)==wanted,'all reports')
  for _,ax in reports:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
  need(output.is_file()and not output.is_symlink(),'regular object');row['axiom_reports']=reports
  save(P/'state.json',state);check(source);guard();print('PASS',source['module'],round(row['seconds'],3),flush=True)
 for z in list(pins.values()):check(z)
 state.update(status='PASS',observed_paths=len(pins),free_bytes=shutil.disk_usage('/tmp').free)
 save(P/'state.json',state);print('PASS',P,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(P/'state.json',state);raise
