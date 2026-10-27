from pathlib import Path
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def rec(p):return dict(path=str(p),sha256=sha(p))
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
loc=Path('/tmp/wordperm222-root-build-location.txt')
if sys.argv[1]=='plan':
 ip=V/'validator-seed-image222-replay.json';i=json.loads(ip.read_text())['inputs'];np=Path('/tmp/current-narrow-native-root-2wv7shqg/plan.json');ns=np.with_name('state.json');pplan=json.loads(np.read_text());st=json.loads(ns.read_text());assert st['status']=='PASS'and sha(np)==st['plan_sha256'];mods={}
 for e in i['modules']:mods[e['module']]=dict(e)
 fresh={e['module']:e for e in st['completed']}
 for e in pplan['modules']:
  n=e['module'];src=e['source'];obj=fresh[n]['object']if n in fresh else e['object']
  if n in mods:assert mods[n]['source_sha256']==src['sha256'];continue
  mods[n]=dict(module=n,source=src['path'],source_sha256=src['sha256'],objects=[obj])
 parserfile=V/'current-positive-zero2011-closure/plan.py';assert sha(parserfile)=='fce21bcc246d82485ef1cf99510eedcce4bf9d90e21c0ae34681ea385cac9a34';sp=importlib.util.spec_from_file_location('parser',parserfile);parser=importlib.util.module_from_spec(sp);sp.loader.exec_module(parser);needed=set();order=[]
 def visit(n):
  if n in needed:return
  needed.add(n);e=mods[n];e['imports']=parser.imports(Path(e['source']))
  for dep in e['imports']:
   if dep in mods:visit(dep)
   else:assert not dep.startswith(('Foundation.','BusyBeaver.','ZFCinPA.','DiophantineConsistency.')),dep
  order.append(n)
 for n in ['BusyBeaver.ZFC.ArithmeticCantor','BusyBeaver.ZFC.EnumPerm']:visit(n)
 p=Path(tempfile.mkdtemp(prefix='wordperm222-root-author-'));lib=p/'lib';lib.mkdir();loc.write_text(str(p));ext=i['lean_path'].split(':')[1:]+[str(Path(i['compiler']).parent.parent/'lib/lean')];pins=[rec(ip),rec(np),rec(ns),rec(parserfile),dict(path=i['compiler'],sha256=i['compiler_sha256']),rec(R/'lake-manifest.json'),rec(R/'lean-toolchain')]
 for n in order:
  e=mods[n];assert sha(e['source'])==e['source_sha256'];pins.append(dict(path=e['source'],sha256=e['source_sha256']))
  for o in e['objects']:
   check(o);pins.append(o);out=lib/Path(*n.split('.')[:-1])/Path(o['path']).name;out.parent.mkdir(parents=True,exist_ok=True);out.symlink_to(o['path'])
 boundaries=[]
 for n in sorted({dep for n in needed for dep in mods[n]['imports']if dep not in mods}):
  q=next((Path(base)/Path(*n.split('.')).with_suffix('.olean')for base in ext if(Path(base)/Path(*n.split('.')).with_suffix('.olean')).is_file()),None);assert q is not None,n
  boundaries.append(dict(module=n,object=rec(q)));pins.append(rec(q))
  for suffix in ['.private','.server','.ir']:
   f=Path(str(q)+suffix)if suffix!='.ir'else q.with_suffix('.ir')
   if f.is_file():pins.append(rec(f))
 for e in pins:check(e)
 d=dict(status='PLANNED',private=str(p),snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),compiler=i['compiler'],compiler_sha256=i['compiler_sha256'],manifest_sha256=sha(R/'lake-manifest.json'),modules=[mods[n]for n in order],external=boundaries,pins=pins,lean_path=':'.join([str(lib),*ext]),driver_sha256=sha(__file__),scope='Exact dependency union for ArithmeticCantor and literal EnumPerm; authenticated reuse only, no dependency/Foundation build.')
 save(p/'inputs.json',d);print(json.dumps(dict(private=str(p),cached=len(order),foundation=sum(n.startswith('Foundation.')for n in order),external=len(boundaries),pins=len(pins))))
elif sys.argv[1]=='run':
 p=Path(loc.read_text());d=json.loads((p/'inputs.json').read_text());assert sha(__file__)==d['driver_sha256'];env=os.environ.copy();env['LEAN_PATH']=d['lean_path'];env.pop('LEAN_SRC_PATH',None)
 for e in d['pins']:check(e)
 records=[]
 for name in ['ArithmeticCommandWordPerm222','ArithmeticCommandWordPerm222Checks']:
  assert shutil.disk_usage(p).free>=512*1024*1024;src=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(name+'.lean');stamp=str(time.time_ns());snap=p/(stamp+'-'+name+'.lean');shutil.copyfile(src,snap);log=p/(stamp+'-'+name+'.log');out=p/'lib/DiophantineConsistency'/(name+'.olean');out.parent.mkdir(parents=True,exist_ok=True);cmd=[d['compiler'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];start=time.time()
  with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  x=dict(module='DiophantineConsistency.'+name,source=rec(src),snapshot=rec(snap),command=cmd,exit_code=code,seconds=time.time()-start,log=rec(log),object=rec(out)if code==0 else None);assert sha(src)==sha(snap);reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());x['axiom_reports']=reports;records.append(x);save(p/(stamp+'-'+name+'.json'),x);print(json.dumps(x),flush=True)
  if code:break
  for title,a in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',a))<={'propext','Classical.choice','Quot.sound'},title
 for e in d['pins']:check(e)
 save(p/('run-'+str(time.time_ns())+'.json'),dict(status='PASS'if len(records)==2 and all(e['exit_code']==0 for e in records)else'FAILED',inputs_sha256=sha(p/'inputs.json'),records=records));assert len(records)==2 and all(e['exit_code']==0 for e in records)
else:raise SystemExit('plan or run')
