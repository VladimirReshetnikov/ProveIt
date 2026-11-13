#!/usr/bin/env python3
"""Bounded, source-pinned experiment; inherits 13-variable provider ancestry."""
import hashlib,importlib.util,json,os,re,shutil,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file());BASE=Path('/tmp/nine-sharing-norm38-current-four-cast-instantiation-check-20261105');OUT=Path('/tmp/nine-sharing-norm38-current-jones-static-check-v2-20261105');SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py';STATE=D/'research/nine-sharing-norm38-current-four-cast-instantiation-check/attempt01/state.json';roots=[OUT/'lib',SPHERE,MODEL,PKG,TOOL];suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']
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
need(not OUT.exists(),'output exists');need(sha(MON)=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad','monitor');need(sha(STATE)=='bad562eeca80d04d60ede99deb281686134612c3c091230a7326dd850b5deabf','bridge receipt');base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==1,'bridge state')
need(sha(P/'source-manifest.json')=='cf5a9b203599b2af0d249a55699c08ef76bf57874595a2d5b1969f2df7f6df6c','manifest pin');manifest=json.loads((P/'source-manifest.json').read_text());entries=manifest['rows'];names=[x['module'].split('.')[-1] for x in entries];pins=[x['source_sha256'] for x in entries]
# Bind the three separately imported slot producers to the recorded successful
# rows of the earlier overall-failed batch, not merely to overlay link paths.
PRODUCER_STATE=D/'research/nine-sharing-norm38-slots-batched-retry01/attempt01/state.json'
PRODUCER=Path('/tmp/nine-sharing-norm38-slots-batched-retry01-20261105')
need(sha(PRODUCER_STATE)=='5e2b9bc0792962fe16bb2015ee035a06c4e806acfeb85eafc2d942029eef8edc','slot producer state')
producer=json.loads(PRODUCER_STATE.read_text());need(producer['status']=='FAILED' and len(producer['rows'])==12 and producer['rows'][-1]['compile']['stop_reason']=='timeout','slot producer shape')
for n in tuple('Norm38Slots%02d'%i for i in range(10)):
 matches=[row for row in producer['rows'][:11] if row['module']==n];need(len(matches)==1,'slot producer row '+n);row=matches[0]
 need(row['deps']['exit']==0 and row['compile']['exit']==0 and row['compile']['stop_reason'] is None,'slot producer exit '+n)
 need(sha(PRODUCER/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(PRODUCER/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'slot producer source/object '+n)
 for phase in ('deps','compile'):need(sha(PRODUCER/(n+'-'+phase+'.txt'))==row[phase]['log_sha256'],'slot producer log '+n)
 for k,v in row['direct_guard'].items():
  path=Path(k)
  if v is None:need(not os.path.lexists(path),'slot producer unexpected '+k)
  else:need(path.is_file() and str(path.resolve())==v['realpath'] and sha(path)==v['sha256'],'slot producer guard '+k)
 overlay=BASE/'lib/DiophantineConsistency'/(n+'.olean');need(overlay.is_symlink() and overlay.resolve()==(PRODUCER/'lib/DiophantineConsistency'/(n+'.olean')).resolve(),'slot overlay route '+n)
# Authenticate the directly used each-slot producer as well as the ten slot groups.
EACH_STATE=D/'research/nine-sharing-norm38-each-slot-retry01/attempt01/state.json'
EACH=Path('/tmp/nine-sharing-norm38-each-slot-retry01-20261105')
need(sha(EACH_STATE)=='8bd674fad57bcb8dfe1d4d98dc8ba5716be15bc7d9c029f39198e53557bdfa70','each-slot state')
each=json.loads(EACH_STATE.read_text());need(each['status']=='PASS' and len(each['rows'])==1,'each-slot receipt');er=each['rows'][0];need(er['module']=='Norm38EachSlot' and er['deps']['exit']==0 and er['compile']['exit']==0,'each-slot status')
need(sha(EACH/'src/DiophantineConsistency/Norm38EachSlot.lean')==er['source_sha256'] and sha(EACH/'lib/DiophantineConsistency/Norm38EachSlot.olean')==er['object_sha256'],'each-slot source/object')
for phase in ('deps','compile'):need(sha(EACH/('Norm38EachSlot-'+phase+'.txt'))==er[phase]['log_sha256'],'each-slot log')
for k,v in er['direct_guard'].items():
 path=Path(k)
 if v is None:need(not os.path.lexists(path),'each-slot unexpected '+k)
 else:need(path.is_file() and str(path.resolve())==v['realpath'] and sha(path)==v['sha256'],'each-slot guard '+k)
overlay=BASE/'lib/DiophantineConsistency/Norm38EachSlot.olean';need(overlay.is_symlink() and overlay.resolve()==(EACH/'lib/DiophantineConsistency/Norm38EachSlot.olean').resolve(),'each-slot overlay route')
# Bind the two other imported theorem producers to their successful receipts.
for label,statepath,rootpath,mod,pin in (
 ('gates',D/'research/nine-sharing-norm38-gates-assembly-retry/attempt01/state.json',Path('/tmp/nine-sharing-norm38-gates-assembly-retry-20261105'),'Norm38GatesAssembly','1ca0968a7e2acfbd398302581e30f3c02caebcf2a4c81081ba73e0b913ea8b72'),
 ('norms',D/'research/nine-sharing-norm38-five-norms-check-v2/attempt01/state.json',Path('/tmp/nine-sharing-norm38-five-norms-check-v2-20261105'),'Norm38FiveNorms','a16e6c80cd1f713b0ec2e863b800847a80265e86643f757ae146c1f1c9656140')):
 need(sha(statepath)==pin,label+' producer state');prod=json.loads(statepath.read_text());need(prod['status']=='PASS' and len(prod['rows'])==1,label+' producer status');row=prod['rows'][0];need(row['module']==mod and row['deps']['exit']==0 and row['compile']['exit']==0 and row['compile']['stop_reason'] is None,label+' producer exits')
 need(sha(rootpath/'src/DiophantineConsistency'/(mod+'.lean'))==row['source_sha256'] and sha(rootpath/'lib/DiophantineConsistency'/(mod+'.olean'))==row['object_sha256'],label+' producer source/object')
 for phase in ('deps','compile'):need(sha(rootpath/(mod+'-'+phase+'.txt'))==row[phase]['log_sha256'],label+' producer log')
 for k,v in row['direct_guard'].items():
  path=Path(k)
  if v is None:need(not os.path.lexists(path),label+' unexpected '+k)
  else:need(path.is_file() and str(path.resolve())==v['realpath'] and sha(path)==v['sha256'],label+' producer guard '+k)
 overlay=BASE/'lib/DiophantineConsistency'/(mod+'.olean');need(overlay.is_symlink() and overlay.resolve()==(rootpath/'lib/DiophantineConsistency'/(mod+'.olean')).resolve(),label+' overlay route')
# Authenticate the separately imported kernel provider from its successful build.
KERNEL_STATE=Path('/tmp/current14-standard-fresh-build-20261104/state.json')
KERNEL_ROOT=Path('/tmp/current14-standard-fresh-build-20261104')
def check_kernel():
 need(sha(KERNEL_STATE)=='f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014','kernel producer state');prod=json.loads(KERNEL_STATE.read_text());need(prod['status']=='PASS','kernel producer status')
 matches=[row for row in prod['records'] if row['module']=='DiophantineConsistency.CurrentKernelData2011'];need(len(matches)==1,'kernel row');row=matches[0];need(row['exit']==0,'kernel exit')
 need(sha(Path(prod['snapshot'])/'src/DiophantineConsistency/CurrentKernelData2011.lean')==row['source_sha256'] and sha(D/'Lean/DiophantineConsistency/CurrentKernelData2011.lean')==row['source_sha256'],'kernel source')
 obj=KERNEL_ROOT/'lib/DiophantineConsistency/CurrentKernelData2011.olean';need(sha(obj)==row['object_sha256']=='95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896' and sha(row['log'])==row['log_sha256'],'kernel object/log')
 for mod,v in row['direct_inputs'].items():need(Path(v['path']).is_file() and sha(v['path'])==v['sha256'],'kernel direct input '+mod)
 selected={k:v for k,v in prod['guarded_companions'].items() if '/CurrentKernelData2011.' in k};need(len(selected)==10,'kernel companion count')
 for k,v in selected.items():
  path=Path(k)
  if v is None:need(not os.path.lexists(path),'kernel unexpected '+k)
  else:need(path.is_file() and str(path.resolve())==v['realpath'] and sha(path)==v['sha256'],'kernel companion '+k)
 overlay=BASE/'lib/DiophantineConsistency/CurrentKernelData2011.olean';need(overlay.is_symlink() and overlay.resolve()==obj.resolve(),'kernel overlay route')
check_kernel()
# Authenticate the separately imported seed/static theorem producer.
IFF_STATE=D/'research/nine-sharing-norm38-seed-static-iff-check/attempt01/state.json'
IFF=Path('/tmp/nine-sharing-norm38-seed-static-iff-check-20261105')
need(sha(IFF_STATE)=='ebc30ad19643e6e0fe5eb5f253163d660c8510165e902d53150e11d75a9be578','iff producer state');iff=json.loads(IFF_STATE.read_text());need(iff['status']=='PASS' and len(iff['rows'])==1,'iff producer status');ir=iff['rows'][0];need(ir['module']=='Norm38SeedStaticIff' and ir['deps']['exit']==0 and ir['compile']['exit']==0,'iff producer exits')
need(sha(IFF/'src/DiophantineConsistency/Norm38SeedStaticIff.lean')==ir['source_sha256'] and sha(IFF/'lib/DiophantineConsistency/Norm38SeedStaticIff.olean')==ir['object_sha256'],'iff source/object')
for phase in ('deps','compile'):need(sha(IFF/('Norm38SeedStaticIff-'+phase+'.txt'))==ir[phase]['log_sha256'],'iff producer log')
for k,v in ir['direct_guard'].items():
 path=Path(k)
 if v is None:need(not os.path.lexists(path),'iff unexpected '+k)
 else:need(path.is_file() and str(path.resolve())==v['realpath'] and sha(path)==v['sha256'],'iff producer guard '+k)
overlay=BASE/'lib/DiophantineConsistency/Norm38SeedStaticIff.olean';need(overlay.is_symlink() and overlay.resolve()==(IFF/'lib/DiophantineConsistency/Norm38SeedStaticIff.olean').resolve(),'iff overlay route')
# Bind all four individually checked current-port projections.
PORT_STATE=D/'research/nine-sharing-norm38-current-ports-split-draft/attempt01/state.json'
PORT=Path('/tmp/nine-sharing-norm38-current-ports-split-20261105')
need(sha(PORT_STATE)=='0f89b8b0a53abd15b0d7c1e20f198495775628e104fabc247c24efbd2cb81ad4','port producer state');prod=json.loads(PORT_STATE.read_text());need(prod['status']=='FAILED' and len(prod['rows'])==6 and prod['rows'][-1]['module']=='Norm38CurrentPortCasts' and prod['rows'][-1]['compile']['exit']==1,'port producer shape')
for n in tuple('Norm38CurrentPort%d'%i for i in range(4)):
 matches=[row for row in prod['rows'][:5] if row['module']==n];need(len(matches)==1,'port producer row '+n);row=matches[0];need(row['deps']['exit']==0 and row['compile']['exit']==0 and row['compile']['stop_reason'] is None,'port producer exits '+n)
 need(sha(PORT/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(PORT/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'port producer source/object '+n)
 for phase in ('deps','compile'):need(sha(PORT/(n+'-'+phase+'.txt'))==row[phase]['log_sha256'],'port producer log '+n)
 for k,v in row['direct_guard'].items():
  path=Path(k)
  if v is None:need(not os.path.lexists(path),'port producer unexpected '+k)
  else:need(path.is_file() and str(path.resolve())==v['realpath'] and sha(path)==v['sha256'],'port producer guard '+k)
 overlay=BASE/'lib/DiophantineConsistency'/(n+'.olean');need(overlay.is_symlink() and overlay.resolve()==(PORT/'lib/DiophantineConsistency'/(n+'.olean')).resolve(),'port overlay route '+n)
# Authenticate the separately produced fixed-port Jones theorem before injection.
JONES_STATE=D/'research/nine-sharing-seed38-current-jones-retry01/attempt01/state.json'
JONES=Path('/tmp/nine-sharing-seed38-current-jones-retry01-20261105')
need(sha(JONES_STATE)=='ca43e7d3588626c70043b8909d6cbf2762784a3132d079ae22d9329485b32d1f','Jones producer state');jd=json.loads(JONES_STATE.read_text());need(jd['status']=='PASS' and len(jd['rows'])==1,'Jones producer status');jr=jd['rows'][0];need(jr['module']=='SharingSeed38CurrentJones' and jr['deps']['exit']==0 and jr['compile']['exit']==0 and jr['compile']['stop_reason'] is None,'Jones producer exits')
need(sha(JONES/'src/DiophantineConsistency/SharingSeed38CurrentJones.lean')==jr['source_sha256'] and sha(JONES/'lib/DiophantineConsistency/SharingSeed38CurrentJones.olean')==jr['object_sha256']=='9a4695880ffc229505e7cf46a77fb436cb1e7d41f132690cdeb6eb72f4836e2e','Jones source/object')
for phase in ('deps','compile'):need(sha(JONES/('SharingSeed38CurrentJones-'+phase+'.txt'))==jr[phase]['log_sha256'],'Jones producer log')
for k,v in jr['direct_guard'].items():
 path=Path(k)
 if v is None:need(not os.path.lexists(path),'Jones unexpected '+k)
 else:need(path.is_file() and str(path.resolve())==v['realpath'] and sha(path)==v['sha256'],'Jones producer guard '+k)
need(not os.path.lexists(BASE/'lib/DiophantineConsistency/SharingSeed38CurrentJones.olean'),'Jones base target collision')
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
jlink=OUT/'lib/DiophantineConsistency/SharingSeed38CurrentJones.olean';need(not os.path.lexists(jlink),'Jones output collision');jlink.symlink_to((JONES/'lib/DiophantineConsistency/SharingSeed38CurrentJones.olean').resolve());links[str(jlink)]=str(jlink.resolve())
for n in names:shutil.copyfile(P/'src/DiophantineConsistency'/(n+'.lean'),OUT/'src/DiophantineConsistency'/(n+'.lean'))
state={'status':'RUNNING','scope':'Bounded single-module current Jones-static composition experiment on captured Jones provider; no new base rebuild, no project-wide dependency load trace, no endpoint. Sampled monitor may miss transient spikes or escaped descendants.','base_state_sha256':sha(STATE),'runner_sha256':sha(__file__),'overlay_links':links,'rows':[]};save()
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
  row['dependencies']=deps;row['direct_guard']=guard(deps)
  for mod,expected,expected_path in (
   ('DiophantineConsistency.Norm38CurrentFourCastInstantiation',base['rows'][0]['object_sha256'],BASE/'lib/DiophantineConsistency/Norm38CurrentFourCastInstantiation.olean'),
   ('DiophantineConsistency.SharingSeed38CurrentJones',jr['object_sha256'],JONES/'lib/DiophantineConsistency/SharingSeed38CurrentJones.olean')):
   dep=deps[mod];obs=row['direct_guard'].get(dep['path']);need(dep['sha256']==expected and dep['realpath']==str(expected_path.resolve()),'direct producer dependency '+mod)
   need(obs is not None and obs['sha256']==expected and obs['realpath']==str(expected_path.resolve()),'direct producer guard '+mod)
  save();log=OUT/(n+'-compile.txt');obj=OUT/'lib/DiophantineConsistency'/(n+'.olean');res=monitor.run(prefix+['--root='+str(OUT/'src'),str(src),'-o',str(obj)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['compile']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'compile failed '+n);need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",log.read_text()) and obj.is_file(),'errors '+n);need(guard(deps)==row['direct_guard'],'guard drift '+n);row['object_sha256']=sha(obj);save()
 for entry,row in zip(entries,state['rows']):
  need(sha(P/'src/DiophantineConsistency'/(row['module']+'.lean'))==entry['source_sha256'] and sha(REPO/entry['source'])==entry['source_sha256'],'final source drift '+row['module'])
  need(sha(OUT/'lib/DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'] and guard(row['dependencies'])==row['direct_guard'],'final provider drift '+row['module'])
 for k,v in links.items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'final overlay drift '+k)
 check_kernel()
 state['status']='PASS';save();print('PASS norm38 current Jones-static composition')
except BaseException as e:
 state['status']='FAILED';state['failure']=repr(e);save();print('FAILED',repr(e));raise
