#!/usr/bin/env python3
"""Sequential 681-source P72 extension of the authenticated current14 base."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=next(p for p in P.parents if (p/'lakefile.toml').is_file());OUT=Path('/tmp/p72-current-base-extension-20261105');BASE=Path('/tmp/current14-standard-fresh-build-20261104');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';SURVEY=D/'research/p72-current-base-source-survey/survey.py';RESULT=D/'research/p72-current-base-source-survey/result.json';MAN=D/'research/current14-standard-fresh-rebuild-preflight/snapshot-manifest.json';WATCH=D/'research/current14-standard-fresh-rebuild-preflight/run-observation.json';IMPORT=D/'research/p72-current-base-external-import-probe/attempt01/state.json';IMPORT_OUT=D/'research/p72-current-base-external-import-probe/attempt01/outer-terminal.json';SUF=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
def no_lean():
 for p in Path('/proc').iterdir():
  if not p.name.isdecimal():continue
  try:
   if (p/'comm').read_text().strip()=='lean' and (p/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X'):return False
  except (FileNotFoundError,ProcessLookupError):continue
 return True
def available():
 for line in Path('/proc/meminfo').read_text().splitlines():
  if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
 raise RuntimeError('missing MemAvailable')
def save():
 tmp=OUT/'progress.tmp';tmp.write_text(json.dumps(state,sort_keys=True,indent=2)+'\n');os.replace(tmp,OUT/'progress.json')
def writejson(p,v):
 tmp=p.with_suffix('.tmp');tmp.write_text(json.dumps(v,sort_keys=True,indent=2)+'\n');os.replace(tmp,p)
pins={WATCH:'5d45638261f749227f6530b55154b7d3c28197e1e04ab0eaffb10876e2fa3475',SURVEY:'7cd42829676156ef3a414e4b462aa461109713661754a39c3440d6371fe6e636',RESULT:'29cb091647eb0800936795ac0494e5cedcbe8d770c076814e8d52f9c7a738954',MAN:'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',BASE/'state.json':'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',IMPORT:'1e5cea4e85ccdc05af1c0407ba4fd598965be89b9ae63604929fd44aeaa831a5',IMPORT_OUT:'816863acb2dd769cc9acea2e3549e5b68a5961c9638ec7baa368d07b242554a2',P/'monitor.py':'d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad',P/'controls.py':'549acb06c7e0a8a80545c4a2e6143ce8b0730974407fe3e9e8382c367ca31c4f',P/'controls-result.json':'11eb2364388e53a42fd9d3175a3b7255f29581093207d7d89257bdc0c8336fd5',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
def checkpins():
 for p,h in pins.items():need(p.is_file() and sha(p)==h,'pin drift '+str(p))
 need(sha(__file__)==driver,'driver drift')
def run_survey():
 q=subprocess.run([sys.executable,'-I','-S','-B',str(SURVEY)],cwd=ROOT,capture_output=True,timeout=600);need(q.returncode==0 and not q.stderr and q.stdout==RESULT.read_bytes(),'source survey changed');return hashlib.sha256(q.stdout).hexdigest()
def inspect(path):
 if not os.path.lexists(path):return None
 need(path.is_file(),'invalid object '+str(path));return {'realpath':str(path.resolve()),'sha256':sha(path)}
def guard(names,roots):
 out={}
 for n in sorted(names):
  for root in roots:
   for suff in SUF:
    f=root/(n.replace('.','/')+suff);out[str(f)]=inspect(f)
 return out
def validate_guard(g):
 for p,expected in g.items():need(inspect(Path(p))==expected,'guard drift '+p)
def base_check():
 s=json.loads((BASE/'state.json').read_bytes());m=json.loads(MAN.read_bytes());w=json.loads(WATCH.read_bytes());need(s['status']=='PASS' and s['source_status']=='CURRENT_AT_FINAL_CHECK' and w['exit']==0 and w['build_status']=='PASS' and w['build_state_sha256']==pins[BASE/'state.json'] and s['manifest_sha256']==pins[MAN],'base status')
 rec={x['module']:x for x in s['records']};shared=set(sources)&set(m['sources']);need(len(shared)==918,'shared source count');checked=set();edges=0;objects=0
 for n in sorted(shared):
  x=rec[n];need(x['exit']==0 and x['source_sha256']==sources[n]['source_sha256'] and sha(Path(x['log']))==x['log_sha256'],'base producer '+n)
  need(sha(ROOT/sources[n]['source'])==sources[n]['source_sha256'],'base workspace source '+n)
  expected=s['outputs'][n];stem=BASE/'lib'/(n.replace('.','/'));need(set(expected)=={str(stem)+suffix for suffix in SUF},'base output inventory '+n)
  main=expected[str(stem)+'.olean'];need(main is not None and main['sha256']==x['object_sha256'],'base object link '+n)
  for path,v in expected.items():need(inspect(Path(path))==v,'base output drift '+path);objects+=1
  need(set(x['direct_inputs'])-{'Init'}==set(sources[n]['imports'])-{'Init'},'base direct names '+n)
  for dep in x['direct_inputs'].values():
   p=Path(dep['path']);edges+=1
   if str(p) not in checked:need(p.is_file() and sha(p)==dep['sha256'],'base direct drift '+str(p));checked.add(str(p))
 return {'shared_modules':len(shared),'output_slots':objects,'direct_edges':edges,'distinct_direct_paths':len(checked)}
need(not OUT.exists() and no_lean(),'output exists or Lean active');need(available()>=10*1024**3 and shutil.disk_usage('/tmp').free>=5_000_000_000,'initial resources');driver=sha(__file__);checkpins();survey=json.loads(RESULT.read_bytes());sources=survey['project_sources'];order=survey['extension_order'];need(survey['status']=='PASS_SOURCE_SURVEY_ONLY' and len(order)==len(set(order))==681 and survey['base_shared']==918,'survey scope');need(run_survey()==pins[RESULT],'survey mismatch');base_before=base_check();external=set(survey['all_declared_externals'])|{'Init'};external_before=guard(external,[PKG,TOOL]);
for n in external:
 choices=[r/(n.replace('.','/')+'.olean') for r in (PKG,TOOL) if (r/(n.replace('.','/')+'.olean')).is_file()];need(choices and len({sha(x) for x in choices})==1,'missing/conflicting external '+n)
need(json.loads(IMPORT.read_bytes())['status']=='PASS' and json.loads(IMPORT_OUT.read_bytes())['exit_code']==0,'import probe status')
if sys.argv[1:]==['--preflight']:
 print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','base_checks':base_before,'external_guard_slots':len(external_before),'scope':'Source and direct provider snapshot preflight only; no Lean or full package-transitive check.'},sort_keys=True));raise SystemExit(0)
need(not sys.argv[1:],'unexpected arguments');OUT.mkdir();(OUT/'rows').mkdir();(OUT/'logs').mkdir();state={'status':'RUNNING','driver_sha256':driver,'survey_sha256':pins[RESULT],'source_snapshot_count':0,'completed':0,'total':len(order),'phase':'setup','base_checks_before':base_before,'scope':'Single source-snapshot extension of current14 base; direct imports/companions and sampled resource checks. Package-transitive, dynamic and between-observation ancestry inherited; not a consistency decision.'};save()
spec=importlib.util.spec_from_file_location('mon',P/'monitor.py');mon=importlib.util.module_from_spec(spec);spec.loader.exec_module(mon)
try:
 links={}
 for root,dirs,files in os.walk(BASE/'lib',followlinks=False,onerror=lambda e:(_ for _ in ()).throw(e)):
  rr=Path(root);need(not any((rr/x).is_symlink() for x in dirs),'base symlink directory')
  for n in files:
   src=rr/n;need(not src.is_symlink() and src.is_file(),'invalid base file');dst=OUT/'lib'/src.relative_to(BASE/'lib');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src);links[str(dst)]=str(src)
 need(len(links)==1016,'base link inventory');writejson(OUT/'base-links.json',links);writejson(OUT/'external-guard-before.json',external_before);state['base_links_sha256']=sha(OUT/'base-links.json');state['external_guard_before_sha256']=sha(OUT/'external-guard-before.json');save()
 snap={}
 for n in order:
  a=ROOT/sources[n]['source'];b=OUT/'src'/(n.replace('.','/')+'.lean');need(sha(a)==sources[n]['source_sha256'],'source drift '+n);b.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(a,b);need(sha(b)==sources[n]['source_sha256'],'snapshot mismatch '+n);snap[n]=sources[n]['source_sha256']
 writejson(OUT/'source-snapshot.json',snap);state['source_snapshot_count']=len(snap);state['source_snapshot_sha256']=sha(OUT/'source-snapshot.json');state['phase']='build';save();roots=[OUT/'lib',PKG,TOOL];env=dict(os.environ,LEAN_PATH=str(OUT/'lib')+':'+str(PKG),LEAN_NUM_THREADS='1')
 for k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(k,None)
 prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M4000','-j1','-DElab.async=false'];produced={}
 for i,n in enumerate(order):
  need(available()>=10*1024**3 and shutil.disk_usage(OUT).free>=5_000_000_000,'stage resources '+n);src=OUT/'src'/(n.replace('.','/')+'.lean');obj=OUT/'lib'/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);need(not os.path.lexists(obj) and sha(src)==snap[n] and sha(ROOT/sources[n]['source'])==snap[n],'source or output '+n)
  state.update(index=i,active=n,phase='deps');save();rec={'index':i,'module':n,'source_sha256':snap[n],'runs':[]};row=OUT/'rows'/f'{i:04d}.json'
  for typ,args in [('deps',['--deps',str(src)]),('compile',['--root='+str(OUT/'src'),str(src),'-o',str(obj)])]:
   state['phase']=typ;save();log=OUT/'logs'/f'{i:04d}-{typ}.txt';m=mon.run(prefix+args,OUT,env,log,rss_limit=5*1024**3,mem_floor=10*1024**3,seconds=180,interval=.1);rec['runs'].append({'command':prefix+args,**m,'log':str(log),'log_sha256':sha(log)});writejson(row,rec);need(m['exit']==0 and m['stop_reason'] is None and not m['monitor_errors'] and not m['observed_descendant_pids'],'Lean '+typ+' failure '+n)
   if typ=='deps':
    actual={};counts={}
    for line in log.read_text().splitlines():
     f=Path(line);hits=[r for r in roots if f.is_relative_to(r)];need(f.is_absolute() and f.is_file() and line.endswith('.olean') and len(hits)==1,'invalid dependency '+line);mod=str(f.relative_to(hits[0]))[:-6].replace('/','.');counts[mod]=counts.get(mod,0)+1;need(mod not in actual or (mod=='Init' and counts[mod]<=2 and actual[mod]['path']==line),'duplicate dependency '+mod);actual[mod]={'path':line,'realpath':str(f.resolve()),'sha256':sha(f)}
    need(set(actual)-{'Init'}==set(sources[n]['imports'])-{'Init'},'direct names '+n)
    for dep,val in actual.items():
     f=Path(val['path']);candidates=[r/(dep.replace('.','/')+'.olean') for r in roots if (r/(dep.replace('.','/')+'.olean')).is_file()];need(candidates and str(candidates[0])==str(f),'route '+dep)
     if dep in order:need(dep in produced and not f.is_symlink() and f.is_relative_to(OUT/'lib') and val['sha256']==produced[dep],'extension provider '+dep)
     elif dep in sources:need(f.is_symlink() and f.is_relative_to(OUT/'lib') and f.resolve().is_relative_to(BASE/'lib'),'base provider '+dep)
     else:
      for root in (PKG,TOOL):
       for suff in SUF:
        path=str(root/(dep.replace('.','/')+suff));need(inspect(Path(path))==external_before[path],'external guard '+path)
    rec['dependencies']=actual;rec['direct_guard']=guard(actual,roots);writejson(row,rec)
  text=(OUT/'logs'/f'{i:04d}-compile.txt').read_text();need(not re.search(r'(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$',text),'compile errors '+n)
  if n in ('DiophantineConsistency.Compact44.IPRAOrdinary72','DiophantineConsistency.Compact44.IPRAOrdinary72P14'):
   expected=['positiveBridge','native_equivalence','standard_equivalence','reference_equivalence'];expected=(['P72P14.zero_iff']+expected if n.endswith('P14') else expected);reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text);need(len(reports)==len(expected),'endpoint report count '+n)
   for (key,val),short in zip(reports,expected):need(key.endswith('.'+short) or key==short,'endpoint report name '+key);need(set(x.strip() for x in val.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},'endpoint axiom '+key)
   rec['axiom_reports']=reports
  need(obj.is_file(),'missing object '+n);need(guard(rec['dependencies'],roots)==rec['direct_guard'],'direct drift '+n);need(sha(src)==snap[n],'snapshot drift '+n);rec['object_sha256']=sha(obj);rec['status']='PASS';produced[n]=rec['object_sha256'];writejson(row,rec);state['completed']=i+1;state['last_row_sha256']=sha(row);state['phase']='completed_stage';save();print('PASS',i+1,'/',len(order),n,flush=True)
 state['phase']='final_audit';save()
 for n,h in snap.items():need(sha(OUT/'src'/(n.replace('.','/')+'.lean'))==h and sha(ROOT/sources[n]['source'])==h,'final source drift '+n)
 for i,n in enumerate(order):
  rec=json.loads((OUT/'rows'/f'{i:04d}.json').read_text());need(rec['status']=='PASS' and rec['module']==n and sha(OUT/'lib'/(n.replace('.','/')+'.olean'))==rec['object_sha256'],'final object drift '+n);validate_guard(rec['direct_guard'])
 for path,target in links.items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'base link drift '+path)
 need(guard(external,[PKG,TOOL])==external_before,'external guard drift');state['base_checks_after']=base_check();need(state['base_checks_after']==base_before,'base drift');need(run_survey()==pins[RESULT],'final survey drift');checkpins();state.update(status='PASS',phase='complete',completed=len(order));save();print('PASS all 681 P72 source-snapshot extension modules',flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
