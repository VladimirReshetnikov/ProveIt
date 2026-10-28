"""Independent two-leaf replay. No prerequisite build or shared output mutation."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
PK=D/'reviews/validator-seed-marker-discharge222-replay.json'
MF=D/'reviews/validator-seed-marker-discharge222-author-replay/FILES.json'
P=D/'research/validator-seed-marker-discharge-cache-plan.json'
pins={};observations=0
def rec(p):
 p=Path(p);p=p if p.is_absolute() else R/p;b=p.read_bytes()
 return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def need(b,m):
 if not b:raise RuntimeError(m)
def check(x):
 global observations
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path'])
 if 'bytes'in x:need(a['bytes']==x['bytes'],'size '+x['path'])
 pins[a['path']]=a;observations+=1;return a
def load(p,h=None):
 if h:check(dict(path=str(p),sha256=h))
 else:check(rec(p))
 return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
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
guard();private=Path(tempfile.mkdtemp(prefix='validator-seed-marker-discharge222-peer-'))
state=dict(status='PREFLIGHT',private=str(private),driver=rec(__file__),records=[])
save(private/'PEER.json',state);shutil.copyfile(__file__,private/'driver.py')
print('PRIVATE',private,flush=True)
try:
 packet=load(PK,'11654cdb234ce5ce5909c2d7037ecbc00c74850bc06abc34e7afd827920d4ea9')
 manifest=load(MF,'3c2427c59180b7ed4574115219065347314472c9bf4edf1e10aa0647bbdef134')
 need(len(manifest)==65,'author65manifest')
 for x in manifest:check(x)
 need(packet['status']=='PASS' and len(packet['attempts'])==8,'frozen author attempts')
 for x in load(packet['plan_manifest']['path'],packet['plan_manifest']['sha256']):check(x)
 attempts=[]
 for at in packet['attempts']:
  st=load(at['state']['path'],at['state']['sha256'])
  inp=load(st['inputs']['path'],st['inputs']['sha256'])
  need(st['status']==at['status'] and st['status'] in ['PASS','FAILED'],'terminal attempt')
  check(st['driver']);need(st['driver']['sha256']=='b76697713c470f010d91d614f3773357c8525667bc88ed3ce97e437818fbd2ac','read author driver')
  for x in inp['pins']:check(x)
  for s in inp['sources']:
   check(s['snapshot']);need(s['sha256']==s['snapshot']['sha256'],'historical source snapshot')
  for row in st['records']:
   for k in ['snapshot','log','timing']:check(row[k])
   if 'object'in row:check(row['object'])
  for x in at['available_unrecorded_outputs']:check(x)
  attempts.append(dict(number=at['number'],status=st['status'],failure=st.get('failure'),state=rec(at['state']['path'])))
 plan=load(P,'47a392b42dfadc0dd778049415bec00530e08c410176f21ee88542be11733354')
 need(plan['counts']==dict(cached_modules=202,foundation=136,artifacts=610,external_boundaries=45),'exact counts')
 for x in plan['observations']:check(x)
 for k in ['compiler','manifest','toolchain','proposal','driver','historical']:check(plan[k])
 mods={m['module']:m for m in plan['modules']};ext={m['module']:m for m in plan['external']}
 seen=set();active=set();used=set();order=[]
 def visit(n):
  if n not in mods:need(n in ext,'unknown boundary '+n);used.add(n);return
  if n in seen:return
  need(n not in active,'cycle');active.add(n);m=mods[n]
  check(dict(path=m['source'],sha256=m['source_sha256']))
  actual=imports(m['source']);need(actual==m.get('actual_imports',m['imports']),'header '+n)
  for child in actual:visit(child)
  for obj in m['objects']:check(obj)
  active.remove(n);seen.add(n);order.append(n)
 for n in plan['direct_imports']:visit(n)
 need(seen==set(mods)and used==set(ext),'exact reachable closure')
 historical=load(plan['historical']['path'])
 m=mods['BoundedPAConsistency.InternalRelativization']
 hs=next(x for x in historical['sources']if x['module']==m['module'])
 check(dict(path=hs['snapshot'],sha256=m['source_sha256']))
 hp=next(x for x in historical['providers']if x['module']=='Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic')
 current=mods[hp['module']]
 need(current['source_sha256']==hp['source_sha256'],'historical direct source')
 need(next(x['sha256']for x in current['objects']if x['path'].endswith('.olean'))==hp['object_sha256'],'historical direct object')
 for p in m['absent_companions']:need(not Path(p).exists(),'historical absence')
 lib=private/'lib';lib.mkdir()
 for n in order:
  for obj in mods[n]['objects']:
   out=lib/Path(*n.split('.')[:-1])/Path(obj['path']).name
   out.parent.mkdir(parents=True,exist_ok=True);need(not out.exists()and not out.is_symlink(),'link collision')
   out.symlink_to(Path(obj['path']).resolve())
 paths=[str(lib),*plan['package_paths']]
 need(all('/.lake/packages/'in p or p=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for p in paths[1:]),'explicit package fallback only')
 providers=[]
 for n,m in list(mods.items())+list(ext.items()):
  for obj in m['objects']if 'objects'in m else[m]:
   rel=Path(*n.split('.')[:-1])/Path(obj['path']).name
   p=next((Path(q)/rel for q in paths if(Path(q)/rel).is_file()),None)
   need(p is not None,'missing actual first provider')
   providers.append(dict(module=n,expected=obj,actual=check(dict(obj,path=str(p)))))
 need(len(providers)==655,'all655 providers')
 final=packet['final'];need(final['status']=='PASS'and len(final['records'])==2,'final full author pair')
 sources=[]
 for row in final['records']:
  for k in ['source','snapshot','object','log','timing']:check(row[k])
  source=check(row['source']);source['module']=row['module']
  snap=private/Path(source['path']).name;shutil.copyfile(source['path'],snap);source['snapshot']=rec(snap);sources.append(source)
 need(imports(sources[0]['path'])==['Init',*plan['direct_imports']],'main imports')
 need(imports(sources[1]['path'])==['Init',sources[0]['module']],'Checks imports')
 save(private/'INPUTS.json',dict(packet=rec(PK),manifest=rec(MF),plan=rec(P),profile=plan,
  author_attempts=attempts,providers=providers,pins=list(pins.values()),sources=sources,
  driver=rec(__file__),LEAN_PATH=paths))
 state.update(status='RUNNING',inputs=rec(private/'INPUTS.json'));save(private/'PEER.json',state)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for source,author,expected in zip(sources,final['records'],[0,14]):
  guard();check(source);check(source['snapshot'])
  out=lib/Path(*source['module'].split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  need(not out.exists()and not out.is_symlink(),'fresh target')
  stem=Path(source['path']).stem;log=private/(stem+'.log');timing=private/(stem+'.time')
  cmd=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),source['path']]
  start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row=dict(module=source['module'],source=source,snapshot=source['snapshot'],command=cmd,
    exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing))
  state['records'].append(row);save(private/'PEER.json',state)
  need(code==0,'compiler '+source['module']);need(out.is_file()and not out.is_symlink(),'fresh regular object')
  txt=log.read_text();reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",txt)
  need(not re.search(r'\b(?:warning|error|sorryAx)\b',txt),'clean diagnostics');need(len(reports)==expected,'all reports')
  for _,ax in reports:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
  need(rec(out)['sha256']==author['object']['sha256'],'byte-identical object')
  need(rec(log)['sha256']==author['log']['sha256'],'identical full log')
  need([list(r)for r in reports]==author['axiom_reports'],'identical full reports')
  row.update(object=rec(out),axiom_reports=reports,author_object_and_full_log_equal=True)
  save(private/'PEER.json',state);print('PASS',source['module'],round(row['seconds'],3),flush=True)
 for x in list(pins.values()):check(x)
 guard();save(private/'final-authentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values())))
 state.update(status='PASS',observations=observations,unique_paths=len(pins),final_authentication=rec(private/'final-authentication.json'))
 save(private/'PEER.json',state);print('PASS',private,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(private/'PEER.json',state);raise
