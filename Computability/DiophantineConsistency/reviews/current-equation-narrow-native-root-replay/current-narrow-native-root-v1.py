from pathlib import Path
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def rec(p):return dict(path=str(p),sha256=sha(p))
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
loc=Path('/tmp/current-narrow-native-root-location.txt')
if sys.argv[1]=='plan':
 ip=V/'current-equation-narrow-native-plan.json';assert sha(ip)=='1ec5da9296a785ca94ed08048713193f90de6705c68498c66cb7fe38426198d9';i=json.loads(ip.read_text());check(i['parent_plan']);check(i['parent_state']);base=json.loads(Path(i['parent_plan']['path']).read_text());bs=json.loads(Path(i['parent_state']['path']).read_text());assert bs['status']=='PASS'
 parents={e['module']:dict(e)for e in base['modules']}
 for e in bs['completed']:parents[e['module']]['object']=e['object']
 parserfile=V/'current-positive-zero2011-closure/plan.py';assert sha(parserfile)=='fce21bcc246d82485ef1cf99510eedcce4bf9d90e21c0ae34681ea385cac9a34';spec=importlib.util.spec_from_file_location('approved_parser',parserfile);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
 mods={e['module']:dict(e)for e in i['modules']};assert len(mods)==478
 for n,e in mods.items():
  check(e['source']);assert parser.imports(Path(e['source']['path']))==e['imports'],n
  if n in parents:
   assert parents[n]['source']['sha256']==e['prior_source_sha256'];assert parents[n]['object']==e['object'];check(e['object'])
 changed={n for n,e in mods.items()if e['source']['sha256']!=e['prior_source_sha256']};assert changed==set(i['changed']);assert len(changed)==7
 seeds=changed|{n for n,e in mods.items()if n not in parents};affected=set(seeds)
 while True:
  new=affected|{n for n,e in mods.items()if any(dep in affected for dep in e['imports'])}
  if new==affected:break
  affected=new
 assert len(affected)==141
 needed=set()
 def visit(n):
  if n in needed:return
  needed.add(n)
  for dep in mods[n]['imports']:
   if dep in mods:visit(dep)
 for n in i['roots']:visit(n)
 assert len(needed)==420;assert affected&needed==set(i['fresh_dependency_order']);assert needed-affected==set(i['reuse_dependency_order'])
 narrowp=Path(json.loads(Path('/tmp/root-frozen-leaf-replay-locations.json').read_text())['current-equation-narrow']);ns=json.loads((narrowp/'state.json').read_text());assert ns['status']=='PASS';data={e['module']:e for e in ns['completed'][:5]};assert len(data)==5
 for n,e in data.items():
  assert e['source_sha256']==mods[n]['source']['sha256'];o=dict(path=e['object'],sha256=e['object_sha256']);check(o);mods[n]['object']=o
 fresh=[n for n in i['fresh_dependency_order']if n not in data];assert len(fresh)==130
 order=i['reuse_dependency_order']+list(data);assert all(n in needed for n in order)
 p=Path(tempfile.mkdtemp(prefix='current-narrow-native-root-'));lib=p/'lib';lib.mkdir();loc.write_text(str(p));pins=base['pins']+[rec(ip),i['parent_plan'],i['parent_state'],rec(narrowp/'state.json'),rec(parserfile)]
 for e in pins:check(e)
 for n in needed:
  e=mods[n];e['action']='fresh'if n in fresh else'narrow-independent-reuse'if n in data else'authenticated-reuse';q=lib/Path(*n.split('.')).with_suffix('.olean');q.parent.mkdir(parents=True,exist_ok=True)
  if n not in fresh:check(e['object']);q.symlink_to(e['object']['path'])
 available=set(needed)-set(fresh)
 for n in fresh:
  assert all(dep not in needed or dep in available for dep in mods[n]['imports']),n
  available.add(n)
 for n in needed-affected:assert not any(dep in affected for dep in mods[n]['imports']),n
 plan=dict(status='PLANNED',source_snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),authorized_uncommitted_move_audit=rec('/tmp/current-narrow-root-move-audit.json'),private=str(p),modules=[mods[n]for n in i['reuse_dependency_order']+i['fresh_dependency_order']],fresh=fresh,compiler=base['compiler'],external_lean_path=base['external_lean_path'],pins=pins,driver_sha256=sha(__file__),scope='420 selected modules:130 fresh native clients,285 authenticated unchanged reuse,5 independently refreshed exact data owners; no umbrella or Foundation rebuild. Narrow Foundation actual-target comparison is separately passed.')
 save(p/'plan.json',plan);print(json.dumps(dict(private=str(p),fresh=len(fresh),cached=290,pins=len(pins))))
elif sys.argv[1]=='run':
 p=Path(loc.read_text());d=json.loads((p/'plan.json').read_text());assert sha(__file__)==d['driver_sha256'];env=os.environ.copy();env['LEAN_PATH']=':'.join([str(p/'lib'),*d['external_lean_path']]);env.pop('LEAN_SRC_PATH',None);mods={e['module']:e for e in d['modules']};fresh=set(d['fresh']);current={n:e['object']for n,e in mods.items()if n not in fresh}
 check(d['authorized_uncommitted_move_audit']);check(d['compiler'])
 for e in d['pins']:check(e)
 for n,e in mods.items():
  check(e['source'])
  if n in current:check(current[n])
 s=dict(status='RUNNING',plan_sha256=sha(p/'plan.json'),driver_sha256=sha(__file__),completed=[]);save(p/'state.json',s)
 try:
  for n in d['fresh']:
   assert shutil.disk_usage(p).free>=512*1024*1024,'512MiB reserve';e=mods[n];check(e['source'])
   for dep in e['imports']:
    if dep in mods:assert dep in current;check(current[dep])
   out=p/'lib'/Path(*n.split('.')).with_suffix('.olean');log=p/(n+'.txt');cmd=[d['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),e['source']['path']];s['active']=dict(module=n,command=cmd,log=str(log));save(p/'state.json',s);start=time.time()
   with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
   x=dict(module=n,source=e['source'],command=cmd,exit_code=code,seconds=time.time()-start,log=rec(log),object=rec(out)if code==0 else None);s['completed'].append(x);s['active']=None;save(p/'state.json',s);assert code==0,n
   reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());x['axiom_reports']=reports
   for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Quot.sound','Classical.choice'},title
   current[n]=x['object'];save(p/'state.json',s);print(json.dumps(dict(module=n,seconds=x['seconds'],reports=len(reports))),flush=True)
  for n,e in mods.items():check(e['source']);check(current[n])
  for e in d['pins']:check(e)
  s['status']='PASS';save(p/'state.json',s);print('PASS',len(s['completed']),flush=True)
 except BaseException as exc:
  s.update(status='FAILED',failure=str(exc));save(p/'state.json',s);raise
else:raise SystemExit('plan or run')
