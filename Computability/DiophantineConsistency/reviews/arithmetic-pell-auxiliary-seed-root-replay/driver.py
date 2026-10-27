from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
PLAN=D/'research/arithmetic-pell-auxiliary-seed-cache-plan.json'
SCOPE=D/'research/arithmetic-pell-auxiliary-seed-proposal.md'
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
guard();P=Path(tempfile.mkdtemp(prefix='arithmetic-pell-auxiliary-seed-root-'))
lib=P/'lib';lib.mkdir();logs=P/'logs';logs.mkdir()
shutil.copyfile(__file__,P/'driver.py')
state=dict(status='PREFLIGHT',private=str(P),driver=rec(P/'driver.py'),records=[])
save(P/'ROOT.json',state)
marker=Path('/tmp/arithmetic-pell-auxiliary-seed-root-runs.json')
runs=json.loads(marker.read_text())if marker.exists()else[]
runs.append(str(P));save(marker,runs);print('PRIVATE',P,flush=True)
try:
 ap=check(dict(path=str(D/'reviews/arithmetic-pell-auxiliary-seed-replay.json'),sha256='7d7346624ade7c38d074d90456c1ba108f33a68466a373514e167110dbba2301'))
 check(dict(path=str(D/'reviews/arithmetic-pell-auxiliary-seed-author.md'),sha256='c5ed1cb2759d48d81d49bf852762a6e13bcf851ef9b6a30a1b493f80b0d58764'))
 author=json.loads(Path(ap['path']).read_text());need(author['status']=='PASS'and len(author['attempts'])==2,'both author attempts')
 author['records']=author['final']['records']
 mf_author=D/'reviews/arithmetic-pell-auxiliary-seed-author-replay/FILES.json'
 check(dict(path=str(mf_author),sha256='d61c3e0be27019191028b3f7901f39221864517b9159228b43313bca6ee6dda1'))
 ar=json.loads(mf_author.read_text());need(len(ar)==43,'all43 author files')
 for z in ar:check(dict(z,path=str(R/z['path'])))
 for k in ['plan','plan_manifest','reauthentication','freeze']:check(author[k])
 for z in author['root_authorization']:check(z)
 for z in author['freeze_attempt1']['files']:check(z)
 fa=json.loads(Path(author['reauthentication']['path']).read_text());need(fa['status']=='PASS','frozen author evidence')
 for z in fa['pins']:check(z)
 for at in author['attempts']:
  check(at['state']);ast=json.loads(Path(at['state']['path']).read_text());check(ast['inputs']);check(ast['driver'])
  for row in ast['records']:
   need(row['source']['sha256']==row['snapshot']['sha256'],'historical source binding')
   need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'history caps')
   for k in ['snapshot','log','timing']:check(row[k])
   if 'object'in row:check(row['object'])
 for row in author['records']:
  need(row['exit_code']==0,'final author status')
  for k in ['source','snapshot','log','timing','object']:check(row[k])
 check(dict(path=str(PLAN),sha256='59de0e399ed01693294f7c5d6363287c5268797619abc9a2f4b42b0f7ebc3e35'))
 check(dict(path=str(SCOPE),sha256='dede501256049cd8cfcc4a44976d77018b74166a0b7d0b452a1bedf7e981556d'));plan=json.loads(PLAN.read_text())
 expected=dict(custom=108,Foundation=95,artifacts=393,external=38,boundary_primaries=38,boundary_companions=76,actual_first_providers=507,fresh_prerequisites=0)
 need(plan['counts']==expected,'exact prerequisite scope')
 for z in plan['pins']:check(z)
 mf=D/'research/arithmetic-pell-auxiliary-seed-plan-FILES.json'
 check(dict(path=str(mf),sha256='0cafc70c5112c819bd12a3a0c44fdd16eebeb289ee08957b45be06634b22a26f'))
 rows=json.loads(mf.read_text());need(len(rows)==5,'complete frozen plan')
 for z in rows:check(dict(z,path=str(R/z['path'])))
 check(dict(path=str(D/'reviews/arithmetic-pell-auxiliary-seed-plan-root.json'),sha256='77164779f6904ff1f6918a76200087f3a5b0d2e57a733b398f49aea10075dd66'))
 check(dict(path=str(D/'reviews/arithmetic-pell-auxiliary-seed-plan-root.md'),sha256='0fb952cd10915a13564b5b99c74d6441cbfd70130d03559fec4e215f69584332'))
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
 need(len(providers)==507,'all507 providers');check(plan['compiler'])
 sources=[dict(module='DiophantineConsistency.'+n,**check(rec(D/('Lean/DiophantineConsistency/'+n+'.lean'))))
  for n in ['ArithmeticPellAuxiliarySeed','ArithmeticPellAuxiliarySeedChecks']]
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
 for source,wanted in zip(sources,[0,5]):
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
