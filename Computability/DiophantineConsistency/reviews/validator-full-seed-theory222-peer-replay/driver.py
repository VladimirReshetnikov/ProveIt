"""Independent final-source review replay: two leaves, no dependency builds."""
import hashlib, json, os, re, shutil, subprocess, tempfile, time
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
REV=ROOT/'Computability/DiophantineConsistency/reviews'
PINS={
 'validator-full-seed-theory222-author.md':'badcc1f85a6d24902e80fb7e0d0822793ee09773344107b5efa945a03e0d0607',
 'validator-full-seed-theory222-replay.json':'a43514a4122ddf304a805511b4ef444b30418c7408eb217882a8d8233f7e0502',
 'validator-full-seed-theory222-cache.json':'f6419623c32fa0870b6dd368fbb2e324cb6a566aea6c38aa5c72d3d71e0c23ad',
 'validator-full-seed-theory222-author-replay/FILES.json':'4f20507b3bafbd9e9158605bf6e162bdbc7bc64ab25d06c50145c5f30fce723b'}
OBS={}
def require(ok,msg):
 if not ok: raise RuntimeError(msg)
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def observe(path,expected,role):
 actual=sha(path);require(actual==expected,role+': '+str(path))
 OBS[str(path)]={'path':str(path),'sha256':actual,'role':role}
def pin(r,role): observe(r['path'],r['sha256'],role)
def save(path,data): Path(path).write_text(json.dumps(data,indent=2)+'\n')
def strip_comments(text):
 out=[];i=depth=0
 while i<len(text):
  if text.startswith('/-',i):depth+=1;out.extend('  ');i+=2
  elif depth and text.startswith('-/',i):depth-=1;out.extend('  ');i+=2
  elif not depth and text.startswith('--',i):
   j=text.find('\n',i);j=len(text) if j<0 else j;out.extend(' '*(j-i));i=j
  else:out.append(text[i] if not depth or text[i]=='\n' else ' ');i+=1
 require(depth==0,'comment balance');return ''.join(out)
def imports(path):
 text=strip_comments(Path(path).read_text())
 result=[] if re.search(r'^\s*prelude\s*$',text,re.M) else ['Init']
 for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',text,re.M):
  result.extend(re.findall(r'[\w.]+',line))
 return list(dict.fromkeys(result))
def rec(path): return {'path':str(path),'sha256':sha(path),'bytes':Path(path).stat().st_size}
for n,h in PINS.items():observe(REV/n,h,'frozen input')
author=json.loads((REV/'validator-full-seed-theory222-replay.json').read_text())
data=json.loads((REV/'validator-full-seed-theory222-cache.json').read_text())
require(author['inputs']==data,'embedded inventory')
bundle=REV/'validator-full-seed-theory222-author-replay'
manifest=json.loads((bundle/'FILES.json').read_text());require(len(manifest)==47,'47 files')
for r in manifest:observe(bundle/r['path'],r['sha256'],'author bundle')
for r in data['inherited_observations']:pin(r,'inherited authentication')
for r in data['parent_receipts']:pin(r,'accepted parent')
for k in ['compiler','manifest','toolchain']:observe(data[k],data[k+'_sha256'],k)
modules={r['module']:r for r in data['modules']};external={r['module']:r for r in data['external']}
require(data['counts']==dict(cached_modules=191,foundation=136,artifacts=599,external_boundaries=45),'counts')
require(len(modules)==191 and sum(n.startswith('Foundation.') for n in modules)==136,'module counts')
require(sum(len(r['objects']) for r in modules.values())==599 and len(external)==45,'artifact counts')
visited=set();boundary=set();active=set()
def visit(n):
 if n not in modules:
  require(n in external,'unlisted import '+n);boundary.add(n);return
 if n in visited:return
 require(n not in active,'import cycle');active.add(n);r=modules[n]
 observe(r['source'],r['source_sha256'],'selected source')
 require(imports(r['source'])==r['imports'],'import header '+n)
 for o in r['objects']:pin(o,'selected object')
 for dep in r['imports']:visit(dep)
 active.remove(n);visited.add(n)
mainimports=['ZFCinPA.SchemaClosure','ZFCinPA.ValidatorSourceFullSeed222','ZFCinPA.ValidatorEqualityImages222']
for n in mainimports:visit(n)
require(visited==set(modules) and boundary==set(external),'exact transitive DAG')
for r in external.values():pin(r,'external boundary')
tracecount=0
for n,r in modules.items():
 for key in ['provenance','accepted_receipt']:
  if isinstance(r.get(key),dict) and 'sha256' in r[key]:pin(r[key],key)
 tr=r.get('trace')
 prov=r.get('provenance')
 if isinstance(prov,dict) and 'extra-foundation-trace-auth.json' in prov.get('path',''):
  traces=json.loads(Path(prov['path']).read_text())
  tr=next(a for a in traces['modules'] if a['module']==n)
 if tr:
  tracecount+=1;observe(tr['trace'],tr['trace_sha256'],'selected Lake trace')
  require(any('4.32.0' in a for a in tr['compiler']),'trace compiler')
  mapping={a['path']:a for a in tr['files']}
  for f in tr['files']:
   pin(f,'trace-authenticated file')
   require(tr['expected'][f['path']]==f['lake_hash'],'Lake hash relation')
  require(mapping[r['source']]['sha256']==r['source_sha256'],'trace source relation')
  for o in r['objects']:require(mapping[o['path']]['sha256']==o['sha256'],'trace object relation')
require(tracecount==39,'39 selected trace bundles')
r=modules['ZFCinPA.SchemaClosure'];hist=json.loads(Path(r['provenance']['path']).read_text())
hs=next(a for a in hist['project_sources'] if a['module']==r['module'])
ho=next(a for a in hist['fresh_modules'] if a['module']==r['module'])
require(hs['source_sha256']==ho['source_sha256']==r['source_sha256'],'historical source relation')
observe(hs['snapshot'],r['source_sha256'],'historical executed source snapshot')
require(ho['sha256']==r['objects'][0]['sha256'],'historical object relation');pin(ho,'historical executed object')
for a in author['completed']:
 require(a['exit_code']==0,'final author result')
 for k in ['source','snapshot','log','timing']:observe(a[k],a[k+'_sha256'],'final author '+k)
 pin(a['object'],'author object')
require(len(author['completed'])==2 and sum(len(a['axiom_reports']) for a in author['completed'])==13,'final audit count')
require(imports(author['completed'][0]['source'])==['Init',*mainimports],'new main header')
require(imports(author['completed'][1]['source'])==['Init','ZFCinPA.ValidatorFullSeedTheory222'],'new check header')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'initial reserve')
out=Path(tempfile.mkdtemp(prefix='validator-full-seed-theory222-peer-'));lib=out/'lib';lib.mkdir()
for n,r in modules.items():
 stem=lib/n.replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
 for o in r['objects']:
  p=Path(o['path']);suffix=p.name[len(n.rsplit('.',1)[-1]):]
  Path(str(stem)+suffix).symlink_to(p.resolve())
paths=[str(lib),*data['lean_path'].split(':')[1:]]
providers=[]
for n,r in modules.items():
 for o in r['objects']:
  rel=Path(*n.split('.')[:-1])/Path(o['path']).name
  found=next((Path(d)/rel for d in paths if (Path(d)/rel).is_file()),None)
  require(found is not None and sha(found)==o['sha256'],'actual provider '+n)
  providers.append({'module':n,'relative':str(rel),'provider':str(found),'sha256':o['sha256']})
for n,r in external.items():
 rel=Path(n.replace('.','/')+'.olean')
 # Init is also supplied by Lean's own default toolchain search path.
 search=paths+[str(Path(data['compiler']).parent.parent/'lib/lean')]
 found=next((Path(d)/rel for d in search if (Path(d)/rel).is_file()),None)
 require(found is not None and sha(found)==r['sha256'],'actual boundary '+n)
 providers.append({'module':n,'relative':str(rel),'provider':str(found),'sha256':r['sha256']})
shutil.copyfile(__file__,out/'driver.py')
shutil.copyfile(REV/'validator-full-seed-theory222-cache.json',out/'inputs.json')
shutil.copyfile(REV/'validator-full-seed-theory222-replay.json',out/'author-packet.json')
save(out/'providers.json',providers)
env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state={'status':'RUNNING','private':str(out),'driver':rec(out/'driver.py'),'inputs':rec(out/'inputs.json'),
 'counts':data['counts'],'trace_bundles':tracecount,'LEAN_PATH':env['LEAN_PATH'],'records':[]}
def persist():
 state['observations']=len(OBS);save(out/'state.json',state);save(out/'observations.json',list(OBS.values()))
def recheck():
 for p in list(OBS.values()):pin(p,'postcheck')
persist();Path('/tmp/validator-full-seed-theory222-peer-latest').write_text(str(out)+'\n')
print('PRIVATE '+str(out),flush=True)
try:
 for a in author['completed']:
  n=a['module'];p=Path(a['source']);observe(p,a['source_sha256'],'target precheck')
  code=strip_comments(p.read_text());require(not re.search(r'\b(sorry|native_decide|axiom)\b',code),'proof shortcut')
  target=lib/(n.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
  require(not target.exists() and not target.is_symlink(),'fresh target')
  snapshot=out/p.name;shutil.copyfile(p,snapshot)
  log=out/(n+'.log');timing=out/(n+'.time')
  recheck();require(shutil.disk_usage('/tmp').free>=512*1024**2,'command reserve')
  command=[data['compiler'],'-M6000','-j1','-DElab.async=false','-o',str(target),str(p)]
  print('START '+n,flush=True);start=time.monotonic()
  with log.open('w') as f:
   result=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
  r={'module':n,'source':rec(p),'snapshot':rec(snapshot),'command':command,'exit_code':result.returncode,
   'seconds':time.monotonic()-start,'log':rec(log),'timing':rec(timing)}
  state['records'].append(r);persist();print(log.read_text(),flush=True)
  require(result.returncode==0,'compile '+n)
  require(target.is_file() and not target.is_symlink(),'regular target')
  r['object']=rec(target)
  reports=[list(a) for a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log.read_text(),re.S)]
  require(reports==a['axiom_reports'],'exact reports')
  require(all(set(re.findall(r'[\w.]+',v))<={'propext','Classical.choice','Quot.sound'} for _,v in reports),'standard axioms')
  require(not re.search(r'\b(warning|error|sorryAx)\b',log.read_text()),'clean diagnostics')
  require(sha(target)==a['object']['sha256'],'byte-identical object')
  require(sha(log)==a['log_sha256'],'byte-identical log')
  r.update(axiom_reports=reports,matches_author=True);persist()
  observe(p,a['source_sha256'],'target postcheck');recheck()
 require(shutil.disk_usage('/tmp').free>=512*1024**2,'final reserve')
 state.update(status='PASS',free_bytes_after=shutil.disk_usage('/tmp').free);persist()
 print('PASS '+str(out),flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));persist();raise
