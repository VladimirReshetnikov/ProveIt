from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';V=D/'reviews'
PLAN=D/'research/c222-dag-rootperm222-cache-plan-20261027.json'
PACK=V/'arithmetic-dag-rootperm222-replay.json'
PINS={};OBS=[]
def require(p,msg):
 if not p:raise RuntimeError(msg)
def rec(p):
 p=Path(p);p=p if p.is_absolute() else R/p
 return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def check(p):
 a=rec(p['path']);require(a['sha256']==p['sha256'],'hash '+p['path']);OBS.append(dict(expected=p,actual=a));PINS[a['path']]=a;return a
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
 require(depth==0,'comments balanced')
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M)for n in line.split()]))
def guard():require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
def read(p,sha):
 check(dict(path=str(p),sha256=sha));return json.loads(Path(p).read_text())
guard();private=Path(tempfile.mkdtemp(prefix='arithmetic-dag-rootperm222-peer-'));lib=private/'lib';lib.mkdir()
state=dict(status='PREFLIGHT',private=str(private),driver=rec(__file__),records=[])
save(private/'PEER.json',state);print('PRIVATE',private,flush=True)
try:
 plan=read(PLAN,'99ab05b4c499f031c65a58fc426777fac55ecc5584cfbd5a790eb2698cbcfa58')
 author=read(PACK,'47136eefb13b4fedd512e160a3538ba7fb96b5d456ebbe47d37805f41680e65a')
 check(dict(path=str(V/'arithmetic-dag-rootperm222-author.md'),sha256='0339bab879cd8860e7cec969c24635e8ab3d808cca727e2e7f1cca6f6184b655'))
 for path,sha,num in [(D/'research/c222-dag-rootperm222-plan-20261027/FILES.json','fda206c80e29dcbd5b0f8cebbbfaa6547600ba3b5bafa8c162ace76f04d47f46',5),(V/'arithmetic-dag-rootperm222-author-replay/FILES.json','dde4d577a10e7197e11b18bee58f0211e94569a2fd2e90a93d988a52312d7531',17)]:
  rows=read(path,sha);require(len(rows)==num,'manifest count')
  for row in rows:check(row)
 freeze=read(V/'arithmetic-dag-rootperm222-author-replay/freeze-authentication.json','5fb255697d3109272c39bbd866a780ecb61919e767894b7fea7cc77125e948e2')
 for o in freeze['observations']:
  require(o['expected']['sha256']==o['actual']['sha256'],'historical substitution byte equality');check(o['actual'])
 for pair in freeze['copies']:
  require(pair['original']['sha256']==pair['saved']['sha256'],'durable copy equality');check(pair['original']);check(pair['saved'])
 for pin in plan['selected_authentication']:check(pin)
 for pin in nested(plan['accepted_macro_supplement']):check(pin)
 check(author['inputs']);authinputs=json.loads(Path(author['inputs']['path']).read_text())
 require(authinputs['profile']==plan,'author final exact profile')
 for pin in authinputs['pins']:check(pin)
 for row in author['final']['records']:
  for key in ['source','snapshot','log','timing','object']:check(row[key])
 require(author['status']=='PASS' and author['final']['status']=='PASS','author passed')
 counts=dict(custom=149,Foundation=95,artifacts=434,external=39,boundary_companion_observations=117,refresh=0)
 require(plan['counts']==counts,'authorized scope')
 mods={m['module']:m for m in plan['modules']};ext={e['module']:e for e in plan['external']};seen=set();active=set();used=set();order=[]
 def visit(n):
  if n not in mods:require(n in ext,'unknown boundary '+n);used.add(n);return
  if n in seen:return
  require(n not in active,'acyclic');active.add(n)
  for child in mods[n]['actual_imports']:visit(child)
  active.remove(n);seen.add(n);order.append(n)
 for n in plan['direct_imports']:visit(n)
 require(seen==set(mods)and used==set(ext)and order==plan['topological_order'],'exact topological DAG')
 traces=[]
 for m in plan['modules']:
  check(m['source']);require(imports(m['source']['path'])==m['actual_imports'],'source header '+m['module'])
  for key in ['provider','inventory_parent']:
   if key in m:check(m[key])
  for o in m['objects']:
   check(o);dest=lib/Path(*m['module'].split('.')[:-1])/Path(o['path']).name
   dest.parent.mkdir(parents=True,exist_ok=True);require(not dest.exists(),'collision');dest.symlink_to(Path(o['path']).resolve())
   if 'expected_lake_hash'in o:
    hp=Path(o['path']+'.hash');require(hp.read_text().strip()==o['expected_lake_hash'],'Lake output hash');check(rec(hp))
  if m['module'].startswith('Foundation.'):
   primary=next(o for o in m['objects']if o['path'].endswith('.olean'));tp=Path(primary['path']).with_suffix('.trace');tr=json.loads(tp.read_text());check(rec(tp))
   require(any('Lean 4.32.0' in str(x) for x in tr['inputs']),'Foundation compiler trace')
   require(any(m['source']['path'] in str(x) for x in tr['inputs']),'Foundation source path trace')
   output=str(tr['outputs'])
   for o in m['objects']:require(o['expected_lake_hash']in output,'Foundation output trace')
   traces.append(dict(module=m['module'],trace=rec(tp)))
 for pin in nested(plan['external']):check(pin)
 paths=[str(lib),*plan['package_paths']]
 require(all('/.lake/packages/'in x or x=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for x in paths[1:]),'only package/toolchain paths')
 providers=[]
 def first_art(n,expected):
  parent=Path(*n.split('.')[:-1]);rel=parent/Path(expected['path']).name
  actual=next((Path(q)/rel for q in paths if(Path(q)/rel).is_file()),None);require(actual is not None,'first artifact exists '+str(rel))
  a=check(dict(path=str(actual),sha256=expected['sha256']));providers.append(dict(module=n,expected=expected,actual=a))
 for n,m in mods.items():
  for o in m['objects']:first_art(n,o)
 for n,e in ext.items():
  first_art(n,e if'path'in e else e['object'])
  for o in e['companion_observations']:first_art(n,o)
 require(len(providers)==434+39+117,'all first-provider artifacts')
 check(plan['compiler']);check(rec(__file__))
 sources=[row['source']for row in author['final']['records']]
 require(imports(sources[0]['path'])==['Init',*plan['direct_imports']],'main imports')
 require(imports(sources[1]['path'])==['Init','BusyBeaver.ZFC.ArithmeticDagRootPerm222'],'check imports')
 save(private/'inputs.json',dict(plan=rec(PLAN),author=rec(PACK),sources=sources,counts=counts,LEAN_PATH=paths,providers=providers,foundation_traces=traces,pins=list(PINS.values()),observations=OBS))
 shutil.copyfile(__file__,private/'driver.py');state.update(status='RUNNING',inputs=rec(private/'inputs.json'),counts=counts,observations=len(OBS));save(private/'PEER.json',state)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for expected,numreports in zip(author['final']['records'],[0,13]):
  guard();source=expected['source'];check(source);module=expected['module'];snap=private/Path(source['path']).name;shutil.copyfile(source['path'],snap)
  out=lib/Path(*module.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);require(not out.exists()and not out.is_symlink(),'fresh regular output')
  log=private/(snap.stem+'.log');timing=private/(snap.stem+'.time');cmd=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),source['path']]
  start=time.monotonic()
  with log.open('w')as f:exitcode=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row=dict(module=module,source=source,snapshot=rec(snap),command=cmd,exit_code=exitcode,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing));state['records'].append(row);save(private/'PEER.json',state)
  require(exitcode==0,'compiler '+module);require(out.is_file()and not out.is_symlink(),'regular target');row['object']=rec(out)
  text=log.read_text();reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
  require(not re.search(r'\b(?:error|warning|sorryAx)\b',text),'diagnostics');require(len(reports)==numreports,'report count')
  for _,ax in reports:require(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
  require(row['object']['sha256']==expected['object']['sha256'],'byte-identical object');require(row['log']['sha256']==expected['log']['sha256'],'byte-identical complete log')
  row.update(axiom_reports=reports,object_byte_identical=True,full_log_byte_identical=True);save(private/'PEER.json',state);check(source);guard();print('PASS',module,round(row['seconds'],3),flush=True)
 for pin in list(PINS.values()):check(pin)
 save(private/'authentication.json',dict(observations=OBS,count=len(OBS),unique_paths=len(PINS),providers=providers))
 state.update(status='PASS',authentication=rec(private/'authentication.json'),final_observations=len(OBS),unique_paths=len(PINS),free_bytes=shutil.disk_usage('/tmp').free);save(private/'PEER.json',state);print('PASS',private,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(private/'PEER.json',state);raise
