#!/usr/bin/env python3
"""Bounded, source-pinned experiment; inherits 13-variable provider ancestry."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file());BASE=Path('/tmp/nine-sharing-norm38-seed-source-composition-check-20261106');OUT=Path('/tmp/nine-sharing-norm38-current-seed-source-check-20261106');SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py';STATE=D/'research/nine-sharing-norm38-seed-source-composition-draft/attempt01/state.json';roots=[OUT/'lib',SPHERE,MODEL,PKG,TOOL];suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']
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
need(sha(D/'research/nine-sharing-norm38-reference-draft/Norm38Reference.lean')=='14103a5da6245030f2e189aa13869514daf4be668bcdd2f521e1ec132f8c8ff0','reference draft');need(sha(P/'provider_preflight.py')=='52cd5c208320f64d809e0ca6731cf00b349080a045fd052c7fa41d87268d408d','provider survey');survey=subprocess.run([sys.executable,'-I','-S','-B',str(P/'provider_preflight.py')],capture_output=True,text=True,timeout=300);need(survey.returncode==0 and json.loads(survey.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY','provider survey run');need(not OUT.exists(),'output exists');need(sha(MON)=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad','monitor');need(sha(STATE)=='9bef14e22cf04c4a9b0810dcd71866c40401a1f49d369e068151dfe2b111ce59','bridge receipt');base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==1,'bridge state')
need(sha(P/'source-manifest.json')=='60a4658bd4ccf35868962afec2517a3448d66bc60302b185989da39ebf5de2ac','manifest pin');manifest=json.loads((P/'source-manifest.json').read_text());entries=manifest['rows'];names=[x['module'].split('.')[-1] for x in entries];pins=[x['source_sha256'] for x in entries]
for row in base['rows']:
 n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0,'bridge stage '+n);need(sha(BASE/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(BASE/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'bridge source/object '+n)
 for key in ('deps','compile'):need(sha(BASE/(n+'-'+key+'.txt'))==row[key]['log_sha256'],'bridge log '+n)
 for k,v in row['direct_guard'].items():
  q=Path(k)
  if v is None:need(not os.path.lexists(q),'bridge unexpected '+k)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'bridge guard '+k)
for k,v in base['overlay_links'].items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'bridge overlay '+k)
for e in entries:
 src=P/'src/DiophantineConsistency'/(e['module'].split('.')[-1]+'.lean');need(sha(src)==e['source_sha256'],'source pin '+e['module'])
 need(sha(REPO/e['source'])==e['source_sha256'],'source original '+e['module'])
# Verify declared dependencies of stages are topologically ordered.
seen=set()
for entry in entries:
 for dep in entry['imports']:
  if dep in [x['module'] for x in entries]:need(dep in seen,'non-topological '+dep)
 seen.add(entry['module'])
# Check the planned union before creating an output tree.
survey_data=json.loads((P/'survey-result.json').read_text());need(len(survey_data['b_only'])==8,'seed overlay inventory')
for rel,rec in survey_data['b_only'].items():
 target=Path(rec['realpath']);need(not os.path.lexists(BASE/'lib'/rel) and target.is_file() and sha(target)==rec['sha256'],'seed overlay candidate '+rel)
 need(all(not os.path.lexists(r/rel) for r in roots[1:]),'seed object shadows other root '+rel)
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
# Inject exactly the current-port-side unique objects from the pinned survey.
for rel,rec in survey_data['b_only'].items():
 q=OUT/'lib'/rel;target=Path(rec['realpath']);need(not os.path.lexists(q) and target.is_file() and sha(target)==rec['sha256'],'seed overlay candidate '+rel)
 need(all(not os.path.lexists(r/rel) for r in roots[1:]),'seed object shadows other root '+rel);q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(target);links[str(q)]=str(target)
for n in names:shutil.copyfile(P/'src/DiophantineConsistency'/(n+'.lean'),OUT/'src/DiophantineConsistency'/(n+'.lean'))
state={'status':'RUNNING','scope':'Bounded current-port seed-to-source specialization on captured Jones provider; no new base rebuild, no project-wide dependency load trace, no endpoint. Sampled monitor may miss transient spikes or escaped descendants.','base_state_sha256':sha(STATE),'runner_sha256':sha(__file__),'overlay_links':links,'rows':[]};save()
try:
 env=dict(os.environ,LEAN_PATH=':'.join(map(str,roots[:-1])),LEAN_NUM_THREADS='1')
 for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
 for n,pin,entry in zip(names,pins,entries):
  src=OUT/'src/DiophantineConsistency'/(n+'.lean');need(sha(src)==pin,'snapshot drift '+n)
  imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M);need(imports==entry['imports'],'source imports '+n);prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M2800','-j1','-DElab.async=false'];row={'module':n,'source_sha256':pin};state['rows'].append(row);save()
  log=OUT/(n+'-deps.txt');res=monitor.run(prefix+['--deps',str(src)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['deps']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'deps failed '+n)
  deps={};counts={}
  for line in log.read_text().splitlines():
   p=Path(line);hits=[r for r in roots if p.is_relative_to(r)];need(p.is_absolute() and p.is_file() and line.endswith('.olean') and len(hits)==1,'bad dep '+line);mod=str(p.relative_to(hits[0]))[:-6].replace('/','.');counts[mod]=counts.get(mod,0)+1;need(mod not in deps or (mod=='Init' and counts[mod]<=2 and deps[mod]['path']==line),'duplicate '+mod);deps[mod]={'path':line,'realpath':str(p.resolve()),'sha256':sha(p)}
  need(set(deps)-{'Init'}==set(imports)-{'Init'},'dependency set '+n)
  for mod,rec in deps.items():
   candidates=[r/(mod.replace('.','/')+'.olean') for r in roots if (r/(mod.replace('.','/')+'.olean')).is_file()];need(candidates and str(candidates[0])==rec['path'],'dependency route '+mod)
  if n=='Norm38FourCastSeedSource':
   f=survey_data['b_only']['DiophantineConsistency/Norm38FourVariablePorts.olean'];expected={'DiophantineConsistency.Norm38SeedSource':(BASE/'lib/DiophantineConsistency/Norm38SeedSource.olean','e4a4092b123ed7dd0b3c6c2d7e88af9447ca3f1a941ded0dba3f656a1edfd766'),'DiophantineConsistency.Norm38FourVariablePorts':(Path(f['realpath']),f['sha256'])}
  elif n=='Norm38CurrentSeedSource':
   previous=state['rows'][0];need(previous['module']=='Norm38FourCastSeedSource' and previous['compile']['exit']==0 and 'object_sha256' in previous,'previous stage');expected={'DiophantineConsistency.Norm38FourCastSeedSource':(OUT/'lib/DiophantineConsistency/Norm38FourCastSeedSource.olean',previous['object_sha256'])}
   for i in range(4):
    mod='Norm38CurrentPort'+str(i);f=survey_data['b_only']['DiophantineConsistency/'+mod+'.olean'];expected['DiophantineConsistency.'+mod]=(Path(f['realpath']),f['sha256'])
  else:raise RuntimeError('unexpected stage '+n)
  row['dependencies']=deps;row['direct_guard']=guard(deps);need(all(deps[k]['sha256']==h and deps[k]['realpath']==str(v.resolve()) and row['direct_guard'][deps[k]['path']]['sha256']==h and row['direct_guard'][deps[k]['path']]['realpath']==str(v.resolve()) for k,(v,h) in expected.items()),'direct producer guard binding');save();log=OUT/(n+'-compile.txt');obj=OUT/'lib/DiophantineConsistency'/(n+'.olean');res=monitor.run(prefix+['--root='+str(OUT/'src'),str(src),'-o',str(obj)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['compile']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'compile failed '+n);need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",log.read_text()) and obj.is_file(),'errors '+n);need(guard(deps)==row['direct_guard'],'guard drift '+n);row['object_sha256']=sha(obj);save()
 for entry,row in zip(entries,state['rows']):
  need(sha(P/'src/DiophantineConsistency'/(row['module']+'.lean'))==entry['source_sha256'] and sha(REPO/entry['source'])==entry['source_sha256'],'final source drift '+row['module'])
  need(sha(OUT/'lib/DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'] and guard(row['dependencies'])==row['direct_guard'],'final provider drift '+row['module'])
 for k,v in links.items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'final overlay drift '+k)
 need(sha(P/'provider_preflight.py')=='52cd5c208320f64d809e0ca6731cf00b349080a045fd052c7fa41d87268d408d','final provider survey source');survey2=subprocess.run([sys.executable,'-I','-S','-B',str(P/'provider_preflight.py')],capture_output=True,text=True,timeout=300);need(survey2.returncode==0 and json.loads(survey2.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY','final provider survey');
 state['status']='PASS';save();print('PASS norm38 current-port seed-to-source specialization')
except BaseException as e:
 state['status']='FAILED';state['failure']=repr(e);save();print('FAILED',repr(e));raise
