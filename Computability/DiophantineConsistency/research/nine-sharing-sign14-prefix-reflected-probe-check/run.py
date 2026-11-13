#!/usr/bin/env python3
"""Bounded, source-pinned experiment; inherits 13-variable provider ancestry."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file());BASE=Path('/tmp/nine-sharing-sign14-prefix-code-check-20261110');OUT=Path('/tmp/nine-sharing-sign14-prefix-reflected-probe-check-20261110');SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py';STATE=D/'research/nine-sharing-sign14-prefix-code-check/attempt01/state.json';roots=[OUT/'lib',SPHERE,MODEL,PKG,TOOL];suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,msg):
 if not x:raise RuntimeError(msg)
def save():
 t=OUT/'state.tmp';t.write_text(json.dumps(state,sort_keys=True,indent=2)+'\n');os.replace(t,OUT/'state.json')
def guard(modules):
 ret={}
 for n in modules:
  for r in roots:
   for s in suffixes:
    p=r/(n.replace('.','/')+s)
    if os.path.lexists(p):need(p.is_file(),'bad candidate '+str(p));ret[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
    else:ret[str(p)]=None
 return ret
def check_external_syntax():
 global framework
 need(sha(P/'framework-survey.py')=='6442c87cf40d2f01578675a2b4107006fca0977864cbe0a714c2dc6515c8d332','framework survey pin')
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'framework-survey.py')],capture_output=True,timeout=120);need(r.returncode==0 and not r.stderr,'framework survey');framework=json.loads(r.stdout);need(framework['status']=='PASS','framework status')
check_external_syntax()
need(sha(D/'research/nine-sharing-sign26-endpoint-retry01/attempt01/state.json')=='8b7490adbdecd01e9d23d3a8978c72d38deb5ef97d931ca1120627acdf2d7003','retry failure receipt')
need(sha(P/'src/DiophantineConsistency/row00.prefix')=='a9d8d3ec099bb64b6146234f605488d1e3d8091666e3a9c9f7507d86b9574bf6' and sha(D/'research/nine-sharing-sign14-prefix-formula/row00.prefix')=='a9d8d3ec099bb64b6146234f605488d1e3d8091666e3a9c9f7507d86b9574bf6','prefix pin')
need(sha(D/'research/nine-sharing-sign14-prefix-rows-check/attempt01/state.json')=='5a04f87b1deb148c9c835067be8addb12d973ad10980c5c4a31beac27a4110a7','prior failure/external audit pin')
need(sha(D/'research/nine-sharing-sign14-prefix-rows-check/attempt01/outer-result.json')=='ec9aff19291e60da9721a17102aff1f281c5f6106b922baeaa313da78ce47100','prior failure/external audit pin')
need(sha(D/'reviews/nine-sharing-sign14-prefix-rows-terminal-independent/check.py')=='32b1c03807598e90a0890e90b7059a7d6e04f207a75a656fd418ee6bc18b8399','prior failure/external audit pin')
need(sha(D/'reviews/nine-sharing-sign14-prefix-formula-independent/check.py')=='32ed3c14ce41659886ccc10ebd79451c091e65c585b34712bb4be57ad7e95170','prior failure/external audit pin')
need(json.loads((D/'research/nine-sharing-sign14-prefix-rows-check/attempt01/outer-result.json').read_text())['author_observed_numeric_outer_exit']==1,'prior failure status')
need(not OUT.exists(),'output exists');need(sha(MON)=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad','monitor');need(sha(STATE)=='06256df1f94947b245672c19a3cc2830e36023e24477a52264b7d521423b30df','bridge receipt');base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==14 and base['rows'][9]['module']=='Sign14PrefixCodeRow00','bridge state')
need(sha(D/'research/nine-sharing-sign14-prefix-code-check/attempt01/outer-result.json')=='1e6462f892a7dd14d86f7e8797cfc40db6984c0ef6fb59541f9a0f7bd2b44805','bridge outer record')
need(sha(D/'reviews/nine-sharing-sign14-prefix-code-terminal-independent/check.py')=='1c9fee1fce741db0a3de137518bb7221328a52dc5698d90e5fa90659c86eb37c','bridge terminal audit checker')
need(json.loads((D/'research/nine-sharing-sign14-prefix-code-check/attempt01/outer-result.json').read_text())['author_observed_numeric_outer_exit']==0,'bridge outer status')
need(sha(P/'source-manifest.json')=='6e2251ce1414f3dafc94eece280ab48d003343e8a4a5a631ff3e49e019821666','manifest pin');manifest=json.loads((P/'source-manifest.json').read_text());entries=manifest['rows'];names=[x['module'].split('.')[-1] for x in entries];pins=[x['source_sha256'] for x in entries]
for row in base['rows']:
 n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0,'bridge stage '+n);need(sha(BASE/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(BASE/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'bridge source/object '+n)
 for key in ('deps','compile'):need(sha(BASE/(n+'-'+key+'.txt'))==row[key]['log_sha256'],'bridge log '+n)
 for k,v in row['direct_guard'].items():
  q=Path(k)
  if v is None:need(not os.path.lexists(q),'bridge unexpected '+k)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'bridge guard '+k)
for k,v in base['overlay_links'].items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'bridge overlay '+k)

for n in ('Sign14PrefixReflectedRow00',):need(not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean')),'candidate target collision '+n)
for e in entries:
 src=P/'src/DiophantineConsistency'/(e['module'].split('.')[-1]+'.lean');need(sha(src)==e['source_sha256'],'source pin '+e['module'])
 need(sha(REPO/e['source'])==e['source_sha256'],'source original '+e['module'])
# Verify declared dependencies of stages are topologically ordered.
seen=set()
for entry in entries:
 for dep in entry['imports']:
  if dep in [x['module'] for x in entries]:need(dep in seen,'non-topological '+dep)
 seen.add(entry['module'])
if sys.argv[1:]==['--preflight']:
 print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','stage_count':len(entries),'scope':'Source/provider point checks only; no Lean, complete transitive trace or model proof.'},sort_keys=True));raise SystemExit(0)
need(not sys.argv[1:],'unexpected arguments')
for proc in Path('/proc').iterdir():
 if not proc.name.isdecimal():continue
 try:need(not ((proc/'comm').read_text().strip()=='lean' and (proc/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X')),'another Lean process is active')
 except (FileNotFoundError,ProcessLookupError):continue
need(shutil.disk_usage('/tmp').free>=5_000_000_000 and int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024>=10*1024**3,'resources')
spec=importlib.util.spec_from_file_location('monitor',MON);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
OUT.mkdir();(OUT/'src/DiophantineConsistency').mkdir(parents=True);(OUT/'lib/DiophantineConsistency').mkdir(parents=True)
links={}
for k,v in base['overlay_links'].items():
 rel=Path(k).relative_to(BASE/'lib');q=OUT/'lib'/rel;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(v);links[str(q)]=v
for row in base['rows']:
 n=row['module'];q=OUT/'lib/DiophantineConsistency'/(n+'.olean');q.symlink_to((BASE/'lib/DiophantineConsistency'/(n+'.olean')).resolve());links[str(q)]=str(q.resolve())
for n in names:shutil.copyfile(P/'src/DiophantineConsistency'/(n+'.lean'),OUT/'src/DiophantineConsistency'/(n+'.lean'))
shutil.copyfile(P/'src/DiophantineConsistency/row00.prefix',OUT/'src/DiophantineConsistency/row00.prefix')
state={'status':'RUNNING','scope':'Bounded sign14 reflected row00 byte binding probe on captured Jones provider; no new base rebuild, no project-wide dependency load trace; endpoint outcome depends on stage results. Sampled monitor may miss transient spikes or escaped descendants.','base_state_sha256':sha(STATE),'runner_sha256':sha(__file__),'overlay_links':links,'rows':[]};save()
try:
 env=dict(os.environ,LEAN_PATH=':'.join(map(str,roots[:-1])),LEAN_NUM_THREADS='1')
 for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
 for n,pin,entry in zip(names,pins,entries):
  src=OUT/'src/DiophantineConsistency'/(n+'.lean');need(sha(src)==pin,'snapshot drift '+n)
  imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M);need(imports==entry['imports'],'source imports '+n);prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M3600','-j1','-DElab.async=false'];row={'module':n,'source_sha256':pin};state['rows'].append(row);save()
  log=OUT/(n+'-deps.txt');res=monitor.run(prefix+['--deps',str(src)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['deps']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'deps failed '+n)
  deps={};counts={}
  for line in log.read_text().splitlines():
   p=Path(line);hits=[r for r in roots if p.is_relative_to(r)];need(p.is_absolute() and p.is_file() and line.endswith('.olean') and len(hits)==1,'bad dep '+line);mod=str(p.relative_to(hits[0]))[:-6].replace('/','.');counts[mod]=counts.get(mod,0)+1;need(mod not in deps or (mod=='Init' and counts[mod]<=2 and deps[mod]['path']==line),'duplicate '+mod);deps[mod]={'path':line,'realpath':str(p.resolve()),'sha256':sha(p)}
  need(set(deps)-{'Init'}==set(imports)-{'Init'},'dependency set '+n)
  for mod,rec in deps.items():
   candidates=[r/(mod.replace('.','/')+'.olean') for r in roots if (r/(mod.replace('.','/')+'.olean')).is_file()];need(candidates and str(candidates[0])==rec['path'],'dependency route '+mod)
  row['dependencies']=deps;row['direct_guard']=guard(deps)
  for mod in imports:
   dep=deps[mod];obs=row['direct_guard'].get(dep['path']);local=mod.split('.')[-1]
   if local=='Sign14PrefixCodeRow00':expected_hash=base['rows'][9]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign14PrefixCodeRow00.olean'
   elif local in ():
    prior=[r for r in state['rows'][:-1] if r['module']==local];need(len(prior)==1,'local producer '+local);expected_hash=prior[0]['object_sha256'];path=OUT/'lib/DiophantineConsistency'/(local+'.olean')
   elif local in framework['observed']:
    rec=framework['observed'][local];expected_hash=rec['sha256'];path=Path(rec['realpath'])
   else:need(False,'unexpected import '+mod)
   need(dep['sha256']==expected_hash and dep['realpath']==str(path.resolve()) and obs is not None and obs['sha256']==dep['sha256'] and obs['realpath']==dep['realpath'],'direct producer binding '+mod)
  save();log=OUT/(n+'-compile.txt');obj=OUT/'lib/DiophantineConsistency'/(n+'.olean');res=monitor.run(prefix+['--root='+str(OUT/'src'),str(src),'-o',str(obj)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['compile']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'compile failed '+n);need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",log.read_text()) and obj.is_file(),'errors '+n);need(guard(deps)==row['direct_guard'],'guard drift '+n);row['object_sha256']=sha(obj);save()
 for entry,row in zip(entries,state['rows']):
  need(sha(P/'src/DiophantineConsistency'/(row['module']+'.lean'))==entry['source_sha256'] and sha(REPO/entry['source'])==entry['source_sha256'],'final source drift '+row['module'])
  need(sha(OUT/'lib/DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'] and guard(row['dependencies'])==row['direct_guard'],'final provider drift '+row['module'])
 for k,v in links.items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'final overlay drift '+k)
 check_external_syntax()
 need(sha(P/'src/DiophantineConsistency/row00.prefix')=='a9d8d3ec099bb64b6146234f605488d1e3d8091666e3a9c9f7507d86b9574bf6' and sha(D/'research/nine-sharing-sign14-prefix-formula/row00.prefix')=='a9d8d3ec099bb64b6146234f605488d1e3d8091666e3a9c9f7507d86b9574bf6' and sha(OUT/'src/DiophantineConsistency/row00.prefix')=='a9d8d3ec099bb64b6146234f605488d1e3d8091666e3a9c9f7507d86b9574bf6','final prefix drift')
 state['status']='PASS';save();print('PASS sign14 reflected row00 probe')
except BaseException as e:
 state['status']='FAILED';state['failure']=repr(e);save();print('FAILED',repr(e));raise
