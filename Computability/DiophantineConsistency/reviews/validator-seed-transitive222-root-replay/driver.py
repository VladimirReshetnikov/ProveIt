from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
P=D/'reviews/validator-seed-transitive222-cache.json'
B=R/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA'
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def need(x,m):
 if not x:raise RuntimeError(m)
def guard():need(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
pins={};obs=0
def check(x):
 global obs
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path'])
 if 'bytes'in x:need(a['bytes']==x['bytes'],'size '+x['path'])
 pins[a['path']]=a;obs+=1;return a
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
guard();private=Path(tempfile.mkdtemp(prefix='validator-seed-transitive222-root-'))
lib=private/'lib';lib.mkdir();state=dict(status='PREFLIGHT',private=str(private),driver=rec(__file__),records=[])
save(private/'ROOT.json',state);shutil.copyfile(__file__,private/'driver.py');print('PRIVATE',private,flush=True)
try:
 AP=D/'reviews/validator-seed-transitive222-replay.json'
 check(dict(path=str(AP),sha256='8d29e8dac0889757e8cdc89bef659907192aa0b45cf7251c3e13e5f88e899bb6'))
 author=json.loads(AP.read_text());need(author['status']=='PASS'and len(author['attempts'])==5,'author chronology')
 check(dict(path=str(D/'reviews/validator-seed-transitive222-author.md'),sha256='eaa9004fdcb0220cacb44973fcb1d38954f56da4173d2f50e3c02f8483962d0c'))
 bundle=Path(author['bundle']);mf=bundle/'FILES.json'
 check(dict(path=str(mf),sha256='94f2eae8b3c632c70ae0e3345955bd0717673676594d9d9aa52dcf31a93fe502'))
 entries=json.loads(mf.read_text());need(len(entries)==63,'all63 author evidence files')
 for x in entries:check(dict(x,path=str(bundle/x['path'])))
 for attempt in author['attempts']:
  at=Path(attempt['path']);check(dict(path=str(at/'state.json'),sha256=attempt['state_sha256']))
  for row in attempt['records']:
   check(dict(path=row['source']['snapshot'],sha256=row['source']['snapshot_sha256']))
   need(row['source']['sha256']==row['source']['snapshot_sha256'],'historical snapshot source')
   for k in ['log','timing']:check(row[k])
   if 'object'in row:check(row['object'])
   need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'historical caps')
 for row in author['completed']:
  check(row['source']);check(dict(path=row['source']['snapshot'],sha256=row['source']['snapshot_sha256']))
  for k in ['log','timing','object']:check(row[k])
 check(dict(path=str(P),sha256='4c3f10084e15adb6c81c55653e0e710ed162e93086b5cc542cf17e9867c18d5d'))
 plan=json.loads(P.read_text());need(plan==author['inputs'],'exact author inventory')
 need(plan['counts']==dict(cached_modules=217,foundation=136,artifacts=625,external_boundaries=45,artifact_providers=670),'exact scope')
 for x in plan['inherited_observations']+plan['observations']:check(x)
 for k in ['compiler','manifest','toolchain','plan','plan_manifest','driver']:check(plan[k])
 pm=Path(plan['plan_manifest']['path']);pmd=json.loads(pm.read_text())
 for x in pmd['files']if isinstance(pmd,dict)else pmd:check(dict(x,path=str(pm.parent/x['path'])))
 direct=['ZFCinPA.ValidatorSeedLogicalImages222']
 mods={m['module']:m for m in plan['modules']};ext={m['module']:m for m in plan['external']}
 seen=set();active=set();used=set();order=[]
 def visit(n):
  if n not in mods:need(n in ext,'unknown boundary '+n);used.add(n);return
  if n in seen:return
  need(n not in active,'cycle');active.add(n);m=mods[n]
  source=check(dict(path=m['source'],sha256=m['source_sha256']))
  actual=imports(source['path']);need(actual==m.get('actual_imports',m['imports']),'header '+n)
  for child in actual:visit(child)
  active.remove(n);seen.add(n);order.append(n)
 for n in direct:visit(n)
 need(seen==set(mods)and used==set(ext),'exact reachable closure')
 for n in order:
  for obj in mods[n]['objects']:
   check(obj);out=lib/Path(*n.split('.')[:-1])/Path(obj['path']).name
   out.parent.mkdir(parents=True,exist_ok=True);need(not out.exists(),'collision');out.symlink_to(Path(obj['path']).resolve())
 paths=[str(lib),*[p for p in plan['package_paths'] if '/.lake/packages/'in p or p=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean']]
 need(all('/.lake/packages/'in p or p=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for p in paths[1:]),'package-only fallback')
 providers=[]
 for n,m in list(mods.items())+list(ext.items()):
  for obj in m['objects']if 'objects'in m else[m]:
   rel=Path(*n.split('.')[:-1])/Path(obj['path']).name
   p=next((Path(root)/rel for root in paths if(Path(root)/rel).is_file()),None)
   need(p is not None,'first provider missing');a=check(dict(obj,path=str(p)));providers.append(dict(module=n,expected=obj,actual=a))
 need(len(providers)==670,'all670 providers')
 sources=[dict(module='ZFCinPA.'+n,**rec(B/(n+'.lean')))for n in ['ValidatorSeedTransitive222','ValidatorSeedTransitive222Checks']]
 need(imports(sources[0]['path'])==['Init',*direct],'main imports')
 need(imports(sources[1]['path'])==['Init',sources[0]['module']],'checks imports')
 for s in sources:
  expected=next(r for r in author['completed']if r['module']==s['module'])
  need(s['sha256']==expected['source']['sha256'],'current final source')
  snap=private/Path(s['path']).name;shutil.copyfile(s['path'],snap);s['snapshot']=rec(snap)
 inputs=dict(plan=rec(P),profile=dict(counts=plan['counts']),providers=providers,pins=list(pins.values()),sources=sources,driver=rec(__file__),LEAN_PATH=paths)
 save(private/'inputs.json',inputs);state.update(status='RUNNING',inputs=rec(private/'inputs.json'));save(private/'ROOT.json',state)
 env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for s,reports_expected in zip(sources,[0,17]):
  guard();check(s);check(s['snapshot']);out=lib/Path(*s['module'].split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  need(not out.exists()and not out.is_symlink(),'fresh regular output')
  stem=Path(s['path']).stem;log=private/(stem+'.log');timing=private/(stem+'.time')
  cmd=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),s['path']];start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row=dict(module=s['module'],source=s,snapshot=s['snapshot'],command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing));state['records'].append(row);save(private/'ROOT.json',state)
  need(code==0,'compiler '+s['module']);need(out.is_file()and not out.is_symlink(),'regular object')
  txt=log.read_text();reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",txt)
  need(not re.search(r'\b(?:warning|error|sorryAx)\b',txt),'clean diagnostics');need(len(reports)==reports_expected,'all reports')
  for _,ax in reports:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
  row.update(object=rec(out),axiom_reports=reports)
  expected=next(r for r in author['completed']if r['module']==row['module'])
  need(row['object']['sha256']==expected['object']['sha256'],'byte-identical author object')
  need(row['log']['sha256']==expected['log']['sha256'],'identical full author log')
  need([list(r)for r in reports]==expected['axiom_reports'],'all reports identical')
  row['author_object_and_full_log_equal']=True
  save(private/'ROOT.json',state);print('PASS',s['module'],round(row['seconds'],3),flush=True)
 for x in list(pins.values()):check(x)
 state.update(status='PASS',observations=obs,unique_paths=len(pins));save(private/'ROOT.json',state);print('PASS',private,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(private/'ROOT.json',state);raise
