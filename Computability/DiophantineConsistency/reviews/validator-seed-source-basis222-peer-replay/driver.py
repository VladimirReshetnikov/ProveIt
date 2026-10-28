from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');REV=R/'Computability/DiophantineConsistency/reviews'
BUNDLE=REV/'validator-seed-source-basis222-author-replay'
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def require(c,m):
 if not c:raise RuntimeError(m)
def guard():require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
def imports(p):
 s=Path(p).read_text();o=[];i=d=0
 while i<len(s):
  q=s[i:i+2]
  if d:
   if q=='/-':d+=1;i+=2
   elif q=='-/':d-=1;i+=2
   else:o.append('\n'if s[i]=='\n'else' ');i+=1
  elif q=='/-':d=1;i+=2
  elif q=='--':
   while i<len(s)and s[i]!='\n':i+=1
  else:o.append(s[i]);i+=1
 require(d==0,'balanced comments');s=''.join(o)
 return list(dict.fromkeys(([]if re.search(r'^\s*prelude\s*$',s,re.M)else['Init'])+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M)for n in re.findall(r'[\w.]+',line)]))
guard();P=Path(tempfile.mkdtemp(prefix='validator-seed-source-basis222-controller-peer-'));LIB=P/'lib';LIB.mkdir()
S=dict(status='PREFLIGHT',private=str(P),driver=rec(__file__),records=[]);save(P/'PEER.json',S);shutil.copyfile(__file__,P/'driver.py');print('PRIVATE',P,flush=True)
OBS=[];PINS={}
def check(p,h,role):
 a=rec(p);require(a['sha256']==h,role+' '+str(p));OBS.append(dict(a,role=role));PINS[a['path']]=a;return a
try:
 packet=REV/'validator-seed-source-basis222-replay.json';check(packet,'c19fcc42ee10f3c48c1d0cc6fed1fb2838ad08538820466516a6c6b37a0c78fa','author packet');A=json.loads(packet.read_text())
 check(REV/'validator-seed-source-basis222-author.md','5975e48c555ea092adee7cad4c0b53d404887ac300ae395de2b3abfd78ccf13e','author receipt')
 check(BUNDLE/'FILES.json','9bbeadf8153e6033bb9d1aae5a0e4def79c08c7c9a12742e057e7a9d0f264f55','117-file manifest')
 files=json.loads((BUNDLE/'FILES.json').read_text());require(len(files)==117,'manifest count')
 byhash={}
 for f in files:
  require(not Path(f['path']).is_absolute()and'..'not in Path(f['path']).parts,'safe manifest path');actual=check(BUNDLE/f['path'],f['sha256'],'author evidence');byhash.setdefault(f['sha256'],[]).append(actual)
 cache=REV/'validator-seed-source-basis222-cache.json';check(cache,A['input_inventory_sha256'],'cache inventory');D=json.loads(cache.read_text());require(D==A['inputs'],'packet/cache identity')
 require(D['counts']==dict(cached_modules=200,foundation=136,artifacts=608,external_boundaries=45),'exact scope')
 require(len(D['inherited_observations'])==952,'route pin count')
 for row in D['inherited_observations']:check(row['path'],row['sha256'],'inherited route observation')
 for name in ['compiler','manifest','toolchain']:check(D[name],D[name+'_sha256'],name)
 for row in D['parent_receipts']:check(row['path'],row['sha256'],'parent receipt')
 M={m['module']:m for m in D['modules']};E={e['module']:e for e in D['external']};seen=set();bound=set();active=set();headers=[]
 def visit(n):
  if n not in M:require(n in E,'unlisted boundary '+n);bound.add(n);return
  require(n not in active,'cycle '+n)
  if n in seen:return
  active.add(n);m=M[n];h=imports(m['source']);require(set(h)==set(m.get('actual_imports',m['imports'])),'header '+n);headers.append(dict(module=n,imports=h))
  for x in h:visit(x)
  active.remove(n);seen.add(n)
 for n in ['ZFCinPA.ValidatorFullSeedTheory222','ZFCinPA.ModelCodedOpenSchemaAxioms']:visit(n)
 require(seen==set(M)and bound==set(E),'exact reachable graph')
 require(len(M)==200 and sum(n.startswith('Foundation.')for n in M)==136 and sum(len(m['objects'])for m in M.values())==608 and len(E)==45,'computed counts')
 for n,m in M.items():
  check(m['source'],m['source_sha256'],'selected source')
  for ob in m['objects']:
   check(ob['path'],ob['sha256'],'selected artifact');dest=LIB/Path(*n.split('.')[:-1])/Path(ob['path']).name;dest.parent.mkdir(parents=True,exist_ok=True);require(not dest.exists(),'duplicate artifact');dest.symlink_to(Path(ob['path']).resolve())
 for e in E.values():check(e['path'],e['sha256'],'external boundary')
 extras=D['lean_path'].split(':')[1:];require(all('/.lake/packages/'in p for p in extras),'no shared project search')
 search=[str(LIB),*extras,str(Path(D['compiler']).parent.parent/'lib/lean')];providers=[]
 for n in [*M,*E]:
  rel=Path(*n.split('.')).with_suffix('.olean');first=next((Path(d)/rel for d in search if(Path(d)/rel).exists()),None);require(first is not None,'missing provider '+n)
  ob=next(o for o in M[n]['objects']if o['path'].endswith('.olean'))if n in M else E[n]
  require(first.resolve()==Path(ob['path']).resolve(),'provider identity '+n);providers.append(dict(module=n,first=check(first,ob['sha256'],'actual first provider')))
 require(len(A['attempts'])==12,'twelve attempts');history=[]
 for attempt in A['attempts']:
  d=BUNDLE/'attempts'/Path(attempt['path']).name;check(d/'state.json',attempt['state_sha256'],'historical state');st=json.loads((d/'state.json').read_text());require(st['status']==attempt['status'],'historical status');hist=dict(path=str(d),status=st['status'],runs=[])
  for row in st['completed']:
   check(d/Path(row['snapshot']).name,row['source_sha256'],'historical source snapshot');check(d/Path(row['log']).name,row['log_sha256'],'historical diagnostics');check(d/Path(row['timing']).name,row['timing_sha256'],'historical timing')
   require(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'historical caps')
   rr=dict(module=row['module'],exit_code=row['exit_code'],source_sha256=row['source_sha256'])
   if 'object'in row:
    ob=row['object']
    if ob['sha256']in byhash:rr['object_evidence']=byhash[ob['sha256']]
    else:rr['object_evidence']=check(ob['path'],ob['sha256'],'preserved successful object')
   hist['runs'].append(rr)
  history.append(hist)
 for row in A['completed']:
  for field in ['source','snapshot','log','timing']:check(row[field],row[field+'_sha256'],'final author '+field)
  check(row['object']['path'],row['object']['sha256'],'final author object')
 require(imports(A['completed'][0]['source'])==['Init','ZFCinPA.ValidatorFullSeedTheory222','ZFCinPA.ModelCodedOpenSchemaAxioms'],'exact main imports')
 require(imports(A['completed'][1]['source'])==['Init','ZFCinPA.ValidatorSeedSourceBasis222'],'exact Checks import')
 save(P/'inputs.json',dict(author_packet=rec(packet),cache=rec(cache),counts=D['counts'],headers=headers,providers=providers,history=history,pins=list(PINS.values()),LEAN_PATH=search))
 save(P/'preflight-observations.json',OBS);S.update(status='RUNNING',inputs=rec(P/'inputs.json'),preflight_observations=len(OBS),counts=D['counts']);save(P/'PEER.json',S)
 env=dict(os.environ,LEAN_PATH=':'.join(search),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for row,count in zip(A['completed'],[0,17]):
  guard();check(row['source'],row['source_sha256'],'executed source before');snap=P/Path(row['source']).name;shutil.copyfile(row['source'],snap)
  out=LIB/Path(*row['module'].split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);require(not out.exists()and not out.is_symlink(),'fresh regular output')
  log=P/(snap.stem+'.log');timing=P/(snap.stem+'.time');cmd=[D['compiler'],'-M6000','-j1','-DElab.async=false','-o',str(out),row['source']]
  start=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  done=dict(module=row['module'],source=rec(row['source']),snapshot=rec(snap),command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing));S['records'].append(done);save(P/'PEER.json',S)
  require(code==0,'fresh compiler '+row['module']);require(out.is_file()and not out.is_symlink(),'regular output')
  txt=log.read_text();reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",txt);require(len(reports)==count,'report count')
  require(not re.search(r'\b(?:warning|error|sorryAx)\b',txt),'clean diagnostics')
  require([list(r)for r in reports]==row['axiom_reports'],'full report equality')
  for _,ax in reports:require(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
  done.update(object=rec(out),object_byte_identical=rec(out)['sha256']==row['object']['sha256'],log_byte_identical=rec(log)['sha256']==row['log_sha256'],axiom_reports=reports)
  check(row['source'],row['source_sha256'],'executed source after');save(P/'PEER.json',S);guard();print('PASS',row['module'],round(done['seconds'],3),'object identical',done['object_byte_identical'],flush=True)
 for pin in list(PINS.values()):check(pin['path'],pin['sha256'],'final reauthentication')
 save(P/'observations.json',OBS);S.update(status='PASS',observations=len(OBS),unique_paths=len(PINS),free_bytes=shutil.disk_usage('/tmp').free);save(P/'PEER.json',S);print('PASS',P,flush=True)
except BaseException as e:
 S.update(status='FAILED',failure=str(e));save(P/'PEER.json',S);save(P/'observations.json',OBS);raise
