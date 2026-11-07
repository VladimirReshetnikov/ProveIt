#!/usr/bin/env python3
"""Bounded, source-pinned experiment; inherits 13-variable provider ancestry."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file());BASE=Path('/tmp/nine-sharing-sign33-seed-squares-check-20261106');OUT=Path('/tmp/nine-sharing-sign32-seed-squares-check-20261106');SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py';STATE=D/'research/nine-sharing-sign33-seed-squares-check/attempt01/state.json';roots=[OUT/'lib',SPHERE,MODEL,PKG,TOOL];suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']
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
draft=D/'research/nine-sharing-sign32-sextic-lean-draft';audit=D/'reviews/nine-sharing-sign32-sextic-lean-frontier-independent';candidate=D/'research/nine-sharing-sign32-sextic-candidate-v2/seed.json'
def check_external_syntax():
 for p,h in ((draft/'SharingSeed32Sextic.lean','83ca02c43152569d1145e32052de74f60e840c16b15e13a55800508fc2c8b0b3'),(draft/'check.py','87d74c5b1cf214e58c3813f8462c1f5a0168b81305138f9914565c0658391936'),(draft/'result.json','05ec66137c443700839fb8d1ab96884c336d7922ae47b03804eea772ce39cb4a'),(audit/'check.py','e2d9229c8d0d521cd27703e09af1ee948ba79bc7c7ec73eee31a7e97510e1477'),(audit/'result.json','f370118d7c4606fb06b94aea21e3fc619836e068b20ee76d5e5929b7a5773d92'),(candidate,'f26172a2cad6e6a8fda042c67821f2fa7651426a62e980173eb5fac07cd835ab')):need(sha(p)==h,'external source/audit pin '+str(p))
syntax_state=D/'research/nine-sharing-sign33-seed-syntax-check/attempt01/state.json'
need(sha(syntax_state)=='7aa987d9f52c5b890e6df924baaa1a723789f2c5fd057491872cac1ca24c3d13','syntax state pin')
syntax=json.loads(syntax_state.read_text());need(syntax['status']=='PASS' and len(syntax['rows'])==1,'syntax state')
producer=syntax['rows'][0];jones=producer['dependencies']['DiophantineConsistency.NineFreshJones'];need(jones['sha256']=='9960f8baa9c5a058d8d472ce1600742bc53fa0030ee78add105b17744912d0df' and sha(jones['realpath'])==jones['sha256'],'Jones producer')
jstate=D/'research/nine-current-fresh-jones-client/attempt01/state.json';need(sha(jstate)=='469b279c32677e416e757dcd59835ea0514d1e524338d3c451ae8cfa8e446439','Jones state pin')
jdata=json.loads(jstate.read_text());need(jdata['status']=='PASS' and len(jdata['rows'])==1,'Jones state');jr=jdata['rows'][0];need(jr['module']=='NineFreshJones' and jr['object_sha256']==jones['sha256'] and jr['deps']['exit']==0 and jr['compile']['exit']==0,'Jones producer binding')
jbase=Path('/tmp/nine-fresh-jones-client-20261105');need(sha(jbase/'src/DiophantineConsistency/NineFreshJones.lean')==jr['source_sha256'] and sha(jbase/'lib/DiophantineConsistency/NineFreshJones.olean')==jr['object_sha256'],'Jones source/object')
for key in ('deps','compile'):need(sha(jbase/('NineFreshJones-'+key+'.txt'))==jr[key]['log_sha256'],'Jones logs '+key)
for k,v in jr['direct_guard'].items():
 q=Path(k)
 if v is None:need(not os.path.lexists(q),'Jones unexpected '+k)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'Jones guard '+k)
obs=producer['direct_guard'].get(jones['path']);need(obs is not None and obs['sha256']==jones['sha256'] and obs['realpath']==jones['realpath'],'syntax Jones observation')
for k,v in producer['direct_guard'].items():
 q=Path(k)
 if v is None:need(not os.path.lexists(q),'syntax unexpected '+k)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'syntax guard '+k)
check_external_syntax()
need(not OUT.exists(),'output exists');need(sha(MON)=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad','monitor');need(sha(STATE)=='b1baa34a7e28603de20eb013e1b6b14e456c3d1ea982cb72a2216ff90a1a1ab0','bridge receipt');base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==1,'bridge state')
need(sha(P/'source-manifest.json')=='d3a79d505051bf33ddd2a40318046fd5b365307f547b8857ff20f8308c280efd','manifest pin');manifest=json.loads((P/'source-manifest.json').read_text());entries=manifest['rows'];names=[x['module'].split('.')[-1] for x in entries];pins=[x['source_sha256'] for x in entries]
for row in base['rows']:
 n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0,'bridge stage '+n);need(sha(BASE/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(BASE/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'bridge source/object '+n)
 for key in ('deps','compile'):need(sha(BASE/(n+'-'+key+'.txt'))==row[key]['log_sha256'],'bridge log '+n)
 for k,v in row['direct_guard'].items():
  q=Path(k)
  if v is None:need(not os.path.lexists(q),'bridge unexpected '+k)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'bridge guard '+k)
for k,v in base['overlay_links'].items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'bridge overlay '+k)

for n in ('SharingSeed32Sextic','SharingSign32Squares'):need(not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean')),'candidate target collision '+n)
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
state={'status':'RUNNING','scope':'Bounded sign32 sum-of-squares residual diagnostic on captured Jones provider; no new base rebuild, no project-wide dependency load trace, no endpoint. Sampled monitor may miss transient spikes or escaped descendants.','base_state_sha256':sha(STATE),'runner_sha256':sha(__file__),'overlay_links':links,'rows':[]};save()
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
  for mod in imports:
   dep=deps[mod];obs=row['direct_guard'].get(dep['path']);local=mod.split('.')[-1]
   if local=='SharingSign33Squares':expected=base['rows'][0];path=BASE/'lib/DiophantineConsistency/SharingSign33Squares.olean';expected_hash=expected['object_sha256']
   elif local=='NineFreshJones':path=Path(jones['realpath']);expected_hash=jones['sha256']
   elif local=='SharingSeed32Sextic':
    prior=[r for r in state['rows'][:-1] if r['module']==local];need(len(prior)==1,'syntax producer');path=OUT/'lib/DiophantineConsistency/SharingSeed32Sextic.olean';expected_hash=prior[0]['object_sha256']
   else:need(False,'unexpected import '+mod)
   need(dep['sha256']==expected_hash and dep['realpath']==str(path.resolve()) and obs is not None and obs['sha256']==dep['sha256'] and obs['realpath']==dep['realpath'],'direct producer binding '+mod)
  save();log=OUT/(n+'-compile.txt');obj=OUT/'lib/DiophantineConsistency'/(n+'.olean');res=monitor.run(prefix+['--root='+str(OUT/'src'),str(src),'-o',str(obj)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['compile']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'compile failed '+n);need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",log.read_text()) and obj.is_file(),'errors '+n);need(guard(deps)==row['direct_guard'],'guard drift '+n);row['object_sha256']=sha(obj);save()
 for entry,row in zip(entries,state['rows']):
  need(sha(P/'src/DiophantineConsistency'/(row['module']+'.lean'))==entry['source_sha256'] and sha(REPO/entry['source'])==entry['source_sha256'],'final source drift '+row['module'])
  need(sha(OUT/'lib/DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'] and guard(row['dependencies'])==row['direct_guard'],'final provider drift '+row['module'])
 for k,v in links.items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'final overlay drift '+k)
 check_external_syntax()
 state['status']='PASS';save();print('PASS sign32 residual-square diagnostic')
except BaseException as e:
 state['status']='FAILED';state['failure']=repr(e);save();print('FAILED',repr(e));raise
