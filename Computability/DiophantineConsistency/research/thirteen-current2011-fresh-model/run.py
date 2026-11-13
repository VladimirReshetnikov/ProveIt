#!/usr/bin/env python3
"""Source-snapshot sequential 13-variable diagnostic; no transitive provenance claim."""
import hashlib,json,os,re,shutil,subprocess,sys,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;ROOT=next(p for p in HERE.parents if (p/'lakefile.toml').is_file());OUT=Path('/tmp/thirteen-current2011-fresh-model-build-20261105');OLD=Path('/tmp/normalized106-fresh-model-build-v2-20261105/lib');SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';PREF=HERE/'preflight.py';MAN=HERE/'preflight-result.json'
EXPECTED_PREF='d61f973a63f89ceb8057ad3c1bf5e652101b9102b0dfc064574cc04d8149c062';EXPECTED_MAN='a796fa2f7752939d862520b50e76fd8fc2f6bbfcdc5cc4337959d94b576a3f0e';SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
def available():
 for line in Path('/proc/meminfo').read_text().splitlines():
  if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
 raise RuntimeError('MemAvailable missing')
def no_lean():
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   if (p/'comm').read_text().strip()=='lean' and (p/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X'):return False
  except (FileNotFoundError,ProcessLookupError):continue
 return True
def preflight(existing=False):
 need(sha(PREF)==EXPECTED_PREF and sha(MAN)==EXPECTED_MAN,'preflight source or receipt drift')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PREF)]+(['--existing-output'] if existing else []),cwd=ROOT,capture_output=True,timeout=600)
 need(q.returncode==0 and not q.stderr and q.stdout==MAN.read_bytes(),'preflight failed or changed '+q.stderr.decode(errors='replace')[-500:]);return hashlib.sha256(q.stdout).hexdigest()
def save():
 p=OUT/'state.tmp';p.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');os.replace(p,OUT/'state.json')
def guard(names):
 result={}
 for n in sorted(names):
  stem=n.replace('.','/')
  for root in roots:
   for suffix in SUFFIXES:
    p=root/(stem+suffix)
    if os.path.lexists(p):need(p.is_file(),'bad candidate '+str(p));result[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
    else:result[str(p)]=None
 return result
def call(label,argv):
 f=OUT/'logs'/(label+'.txt');start=time.monotonic()
 with f.open('x') as stream:q=subprocess.run(prefix+argv,cwd=OUT/'src',env=env,stdout=stream,stderr=subprocess.STDOUT)
 rec={'command':prefix+argv,'exit':q.returncode,'seconds':round(time.monotonic()-start,3),'log':str(f),'log_sha256':sha(f)};return rec
need(not OUT.exists(),'refusing existing output');need(no_lean(),'another Lean process exists');need(available()>=10*1024**3 and shutil.disk_usage('/tmp').free>=5_000_000_000,'prelaunch resources');runner_hash=sha(__file__);prior=preflight();manifest=json.loads(MAN.read_text());need(manifest['status']=='PASS_SOURCE_PREFLIGHT_NOT_BUILD' and len(manifest['stages'])==10,'manifest')
OUT.mkdir();(OUT/'src').mkdir();(OUT/'lib').mkdir();(OUT/'logs').mkdir();state={'status':'RUNNING','runner_sha256':runner_hash,'manifest_sha256':EXPECTED_MAN,'preflight_before_sha256':prior,'records':[],'active':None,'scope':'Single sequential source-snapshot diagnostic. Exact declared/direct paths, companion observations and source-bound objects. No full package-transitive or dynamic load trace, no atomic protection against transient changes, and no automatic group-RSS or host-memory stop. GNU foreground timeout acts on direct child only.'};save()
try:
 links={}
 for root,dirs,files in os.walk(OLD,followlinks=False,onerror=lambda e:(_ for _ in ()).throw(e)):
  r=Path(root);rel=r.relative_to(OLD);need(not any((r/x).is_symlink() for x in dirs),'base symlink directory')
  for x in dirs:(OUT/'lib'/rel/x).mkdir(parents=True,exist_ok=True)
  for x in files:
   p=r/x;q=OUT/'lib'/rel/x;need(p.is_file(),'bad base file');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(p.resolve(strict=True));links[str(q)]=str(p.resolve(strict=True))
 state['base_link_count']=len(links);need(len(links)==1016,'unexpected base inventory');state['base_links_sha256']=hashlib.sha256(json.dumps(links,sort_keys=True).encode()).hexdigest()
 stages=manifest['stages'];stage_names=[x['module'] for x in stages];snap={}
 for row in stages:
  name=row['module'];src=Path(row['source']);need(sha(src)==row['sha256'],'source changed '+name);dst=OUT/'src'/(name.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);need(sha(dst)==row['sha256'],'source copy mismatch '+name);snap[name]=row['sha256']
 state['snapshot']=snap;save();roots=[OUT/'lib',SPHERE,MODEL,PKG,TOOL];env=dict(os.environ,LEAN_PATH=':'.join(map(str,roots[:-1])),LEAN_NUM_THREADS='1')
 for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
 prefix=['/usr/bin/timeout','--foreground','--signal=TERM','--kill-after=5s','180s','/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M2800','-j1','-DElab.async=false'];produced={}
 for i,row in enumerate(stages):
  name=row['module'];need(available()>=10*1024**3 and shutil.disk_usage(OUT).free>=5_000_000_000,'stage resources '+name);src=OUT/'src'/(name.replace('.','/')+'.lean');obj=OUT/'lib'/(name.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);need(not os.path.lexists(obj) and sha(src)==snap[name],'source or output occupied '+name)
  for suffix in SUFFIXES:need(not os.path.lexists(obj.with_name(obj.name[:-6]+suffix)),'output companion occupied '+name)
  state['active']={'module':name,'phase':'deps'};save();dr=call(f'{i:02d}-{name.replace(".","_")}-deps',['--deps',str(src)]);state['active']['deps_run']=dr;save();need(dr['exit']==0,'deps failed '+name)
  actual={};counts={}
  for line in Path(dr['log']).read_text().splitlines():
   p=Path(line);hits=[root for root in roots if p.is_relative_to(root)];need(p.is_absolute() and p.is_file() and line.endswith('.olean') and len(hits)==1,'bad deps line '+line);mod=str(p.relative_to(hits[0]))[:-6].replace('/','.');counts[mod]=counts.get(mod,0)+1
   need(mod not in actual or (mod=='Init' and counts[mod]<=2 and actual[mod]['path']==line),'duplicate dependency '+mod);actual[mod]={'path':line,'realpath':str(p.resolve()),'sha256':sha(p)}
  need(set(actual)-{'Init'}==set(row['imports'])-{'Init'},'declared deps mismatch '+name)
  for mod,rec in actual.items():
   if mod=='Init':continue
   if mod in stage_names:
    need(mod in produced and rec['path']==str(OUT/'lib'/(mod.replace('.','/')+'.olean')) and rec['sha256']==produced[mod],'stage routing '+mod)
   else:
    expected=row['existing_direct'][mod];old=Path(expected['selected']);expected_path=OUT/'lib'/old.relative_to(OLD) if old.is_relative_to(OLD) else old
    need(rec['path']==str(expected_path) and rec['realpath']==expected['realpath'] and rec['sha256']==expected['sha256'],'baseline routing '+mod)
  before=guard(actual);state['active'].update(phase='compile',dependencies=actual,direct_guard_before=before);save();cr=call(f'{i:02d}-{name.replace(".","_")}-compile',['--root='+str(OUT/'src'),str(src),'-o',str(obj)]);state['active']['compile_run']=cr;save();text=Path(cr['log']).read_text();need(cr['exit']==0 and obj.is_file(),'compile failed '+name);need(not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',text),'error or sorry '+name);need(sha(src)==snap[name] and guard(actual)==before,'source or dependency drift '+name)
  reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
  if name=='FrontierChecks':
   expected=['DiophantineConsistency.ModelThirteenForms.standard_equivalence70','DiophantineConsistency.ModelThirteenForms.standard_equivalence71'];need([x for x,_ in reports]==expected,'missing endpoint reports');need(all(not ({x.strip() for x in a.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}) for _,a in reports),'unexpected endpoint axiom')
  produced[name]=sha(obj);state['records'].append({'module':name,'source_sha256':snap[name],'deps_run':dr,'compile_run':cr,'dependencies':actual,'direct_guard':before,'object_sha256':produced[name],'warnings':[x for x in text.splitlines() if 'warning:' in x],'axiom_reports':reports});state['active']=None;save();print('PASS',i+1,name,flush=True)
 for row in stages:need(sha(OUT/'src'/(row['module'].replace('.','/')+'.lean'))==snap[row['module']] and sha(Path(row['source']))==snap[row['module']],'final source drift '+row['module'])
 for rec in state['records']:need(guard(rec['dependencies'])==rec['direct_guard'] and sha(OUT/'lib'/(rec['module'].replace('.','/')+'.olean'))==rec['object_sha256'],'final artifact drift '+rec['module'])
 for path,target in links.items():p=Path(path);need(p.is_symlink() and str(p.resolve())==target,'overlay link drift '+path)
 state['preflight_after_sha256']=preflight(True);need(sha(__file__)==runner_hash,'runner changed');state['status']='PASS';save();print('PASS 13-variable stages and axiom reports',flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
