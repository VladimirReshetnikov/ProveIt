"""Independent source-authenticated two-leaf replay; no dependency compiler."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time,copy
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');REV=ROOT/'Computability/DiophantineConsistency/reviews'
PINS={
 'arithmetic-control-bisim-perm215-author.md':'691b3fbfaa027c88284c4ae54f3475eb6a8e54c84492e850215d4ceb4d45cb68',
 'arithmetic-control-bisim-perm215-replay.json':'5771db7650be9a5b85a8e093b05f11b65d17b7d5abae9640ad8a2f314bc5d862',
 'arithmetic-control-bisim-perm215-author-replay/FILES.json':'97da04e2f77d7e75e1b717daf1aafeadeb1026a4b43d2fdb53d0f32f349c7e9c'}
OBS={}
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def check(r,role='pin'):
 a=rec(r['path']);require(a['sha256']==r['sha256'],role+' '+r['path'])
 OBS[a['path']]=dict(a,role=role);return a
def nested(x):
 if isinstance(x,dict):
  if 'path' in x and 'sha256' in x:yield x
  for v in x.values():yield from nested(v)
 elif isinstance(x,list):
  for v in x:yield from nested(v)
def strip_comments(s):
 out=[];i=depth=0
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
 require(depth==0,'comment balance');return ''.join(out)
def imports(p):
 s=strip_comments(Path(p).read_text());ns=[] if re.search(r'^\s*prelude\s*$',s,re.M) else ['Init']
 for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M):ns.extend(line.split())
 return list(dict.fromkeys(ns))
def save(p,v):Path(p).write_text(json.dumps(v,indent=2)+'\n')
for n,h in PINS.items():check(dict(path=str(REV/n),sha256=h),'author input')
author=json.loads((REV/'arithmetic-control-bisim-perm215-replay.json').read_text())
manifest=json.loads((REV/'arithmetic-control-bisim-perm215-author-replay/FILES.json').read_text())
require(len(manifest)==23,'23 author files')
for r in manifest:check(dict(r,path=str(ROOT/r['path'])),'author bundle')
for key in ['final_inputs','authentication','source_audit','final_data_audit','generator','original_plan','compiler','driver']:check(author[key],key)
data=json.loads(Path(author['final_inputs']['path']).read_text());plan=json.loads(Path(author['original_plan']['path']).read_text())
require(data['counts']==author['counts']==dict(custom=141,Foundation=95,artifacts=426,external=39,fresh_prerequisites=0),'scope')
for pin in plan['pins']+data['pins']:check(pin,'inherited authentication')
sup=author['provider_supplement'];require(sup==data['provider_supplement'],'supplement identity')
check(sup['root_state']);check(sup['root_manifest'])
rstate=json.loads(Path(sup['root_state']['path']).read_text());require(rstate['status']=='PASS','root PASS')
rman=Path(sup['root_manifest']['path'])
for r in json.loads(rman.read_text()):
 q=Path(r['path']);q=q if q.is_absolute() else rman.parent/q
 if not q.exists():q=ROOT/r['path']
 check(dict(r,path=str(q)),'root evidence')
original={r['module']:r for r in plan['modules']};mods={r['module']:r for r in data['modules']}
table=author['accepted_table_supplement'];require(table==data['accepted_table_supplement'],'accepted table identity')
require(table['root_commit']=='048399e422','accepted table commit')
for r in nested(table):check(r,'accepted table supplement')
for r in json.loads(Path(table['root_manifest']['path']).read_text()):check(dict(r,path=str(ROOT/r['path'])),'table ROOT evidence')
newname='BusyBeaver.ZFC.ArithmeticControl215Table'
require(set(mods)==set(original)|{newname},'only accepted table added')
newrow=mods[newname]
require(newrow['source']==table['source'] and newrow['objects']==[table['object']],'accepted table source/object')
require(newrow['actual_imports']==['Init','BusyBeaver.ZFC.ArithmeticDagControlPerm222','BusyBeaver.ZFC.KSource215Program'],'accepted table imports')
changed={c['module']:c for c in sup['changes']}
require(set(changed)=={'BusyBeaver.ZFC.PackedTables','BusyBeaver.ZFC.ArithmeticDagControlPerm222'},'only accepted two providers')
for n,r in mods.items():
 expected=copy.deepcopy(original[n]) if n in original else copy.deepcopy(newrow)
 if n in changed:
  c=changed[n];rr=next(x for x in rstate['records'] if x['module']==n)
  require(c['historical_objects']==expected['objects'],'historical provider pin')
  require(rr['source']['sha256']==expected['source']['sha256'],'root source binding')
  require(c['accepted_object']==rr['object'],'root object binding')
  require(c['accepted_object']['sha256']==expected['objects'][0]['sha256'],'root byte equality')
  expected['objects']=[c['accepted_object']]
 require(r==expected,'explicit provider delta '+n)
 check(r['source'],'selected source')
 if isinstance(r['provider'],dict):check(r['provider'],'provider evidence')
 require(imports(r['source']['path'])==r['actual_imports'],'source header '+n)
 for o in r['objects']:check(o,'cached artifact')
external={r['module']:r for r in data['external']}
require(len(mods)==141 and sum(n.startswith('Foundation.') for n in mods)==95,'module counts')
require(sum(len(r['objects']) for r in mods.values())==426 and len(external)==39,'artifact counts')
for e in nested(data['external']):check(e,'external')
seen=set();used=set();active=set()
def visit(n):
 if n not in mods:require(n in external,'missing import '+n);used.add(n);return
 if n in seen:return
 require(n not in active,'cycle');active.add(n)
 for dep in mods[n]['actual_imports']:visit(dep)
 active.remove(n);seen.add(n)
for n in data['direct_imports']:visit(n)
require(seen==set(mods) and used==set(external),'exact reachable DAG')
for a in author['records']:
 require(a['exit_code']==0,'author result')
 for key in ['source','snapshot','object','log','timing']:check(a[key],'author final')
require(imports(author['records'][0]['source']['path'])==['Init',*data['direct_imports']],'new main imports')
require(imports(author['records'][1]['source']['path'])==['Init',author['records'][0]['module']],'new Checks imports')
audit=json.loads(Path('/tmp/control-bisim-perm215-root-data.json').read_text())
require(audit['status']=='PASS','independent all-row audit')
for r in audit['sources']:check(r,'data-audited source')
check(audit['script'],'executed data checker')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'initial reserve')
out=Path(tempfile.mkdtemp(prefix='control-bisim-perm215-root-'));lib=out/'lib';lib.mkdir()
for n,r in mods.items():
 for obj in r['objects']:
  dest=lib/Path(*n.split('.')[:-1])/Path(obj['path']).name
  dest.parent.mkdir(parents=True,exist_ok=True);require(not dest.exists(),'duplicate artifact');dest.symlink_to(Path(obj['path']).resolve())
paths=[str(lib),*author['LEAN_PATH'][1:]]
require(all('/.lake/packages/' in p or p=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean' for p in paths[1:]),'package boundary paths')
providers=[]
for n,r in list(mods.items())+list(external.items()):
 objects=r['objects'] if n in mods else [r if 'path' in r else r['object']]
 for obj in objects:
  rel=Path(*n.split('.')[:-1])/Path(obj['path']).name
  first=next((Path(p)/rel for p in paths if (Path(p)/rel).is_file()),None)
  require(first is not None and rec(first)['sha256']==obj['sha256'],'actual first provider '+n)
  providers.append({'module':n,'actual':rec(first),'expected':obj})
for src,name in [(Path(__file__),'driver.py'),(Path(author['final_inputs']['path']),'inputs.json'),
 (REV/'arithmetic-control-bisim-perm215-replay.json','author-packet.json'),(Path('/tmp/control-bisim-perm215-root-data.py'),'data-audit.py'),
 (Path('/tmp/control-bisim-perm215-root-data.json'),'data-audit.json'),(Path('/tmp/control-bisim-perm215-root-data.log'),'data-audit.log')]:shutil.copyfile(src,out/name)
save(out/'providers.json',providers)
state={'status':'RUNNING','private':str(out),'driver':rec(out/'driver.py'),'inputs':rec(out/'inputs.json'),'counts':data['counts'],'LEAN_PATH':paths,'records':[]}
def persist():
 state['observations']=len(OBS);save(out/'state.json',state);save(out/'pins.json',list(OBS.values()))
def recheck():
 for r in list(OBS.values()):check(r,'postcheck')
persist();Path('/tmp/control-bisim-perm215-root-latest').write_text(str(out)+'\n');print('PRIVATE '+str(out),flush=True)
env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for a in author['records']:
  src=a['source'];check(src,'target before');recheck();require(shutil.disk_usage('/tmp').free>=512*1024**2,'command reserve')
  n=a['module'];snap=out/Path(src['path']).name;shutil.copyfile(src['path'],snap)
  target=lib/(n.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
  require(not target.exists() and not target.is_symlink(),'fresh output')
  log=out/(snap.stem+'.log');timing=out/(snap.stem+'.time')
  command=[author['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(target),src['path']]
  print('START '+n,flush=True);start=time.monotonic()
  with log.open('w') as f:
   result=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
  r={'module':n,'source':src,'snapshot':rec(snap),'command':command,'exit_code':result.returncode,'seconds':time.monotonic()-start,'log':rec(log),'timing':rec(timing)}
  state['records'].append(r);persist();print(log.read_text(),flush=True)
  require(result.returncode==0,'compile '+n);require(target.is_file() and not target.is_symlink(),'regular output')
  reports=[list(x) for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())]
  require(reports==a['axiom_reports'],'exact reports')
  require(all(set(re.findall(r'[A-Za-z][A-Za-z.]*',x))<={'propext','Classical.choice','Quot.sound'} for _,x in reports),'standard axioms')
  require(not re.search(r'\b(warning|error|sorryAx)\b',log.read_text()),'diagnostics')
  require(rec(target)['sha256']==a['object']['sha256'],'object equality')
  require(rec(log)['sha256']==a['log']['sha256'],'log equality')
  r.update(object=rec(target),axiom_reports=reports,matches_author=True);check(src,'target after');recheck();persist()
 require(shutil.disk_usage('/tmp').free>=512*1024**2,'final reserve')
 state.update(status='PASS',free_bytes=shutil.disk_usage('/tmp').free);persist();print('PASS '+str(out),flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));persist();raise
