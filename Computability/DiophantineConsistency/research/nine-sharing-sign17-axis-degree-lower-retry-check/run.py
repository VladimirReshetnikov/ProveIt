#!/usr/bin/env python3
"""Bounded, source-pinned experiment; inherits 13-variable provider ancestry."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file());BASE=Path('/tmp/nine-sharing-sign17-degree-staged-retry-20261110');OUT=Path('/tmp/nine-sharing-sign17-axis-degree-lower-retry-20261110');SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py';STATE=D/'research/nine-sharing-sign17-degree-staged-retry-check/attempt01/state.json';roots=[OUT/'lib',SPHERE,MODEL,PKG,TOOL];suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']
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
 need(sha(P/'framework-survey.py')=='953e4e5c493a4195919d4f4e4baac054fa801c09c456d8d0fa6453ea5d08360c','framework survey pin')
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'framework-survey.py')],capture_output=True,timeout=120);need(r.returncode==0 and not r.stderr,'framework survey');framework=json.loads(r.stdout);need(framework['status']=='PASS','framework status')
check_external_syntax()
need(sha(D/'research/nine-sharing-sign26-endpoint-retry01/attempt01/state.json')=='8b7490adbdecd01e9d23d3a8978c72d38deb5ef97d931ca1120627acdf2d7003','retry failure receipt')
need(not OUT.exists(),'output exists');need(sha(MON)=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad','monitor');need(sha(STATE)=='fd086fe7412866bb9d2b9211d99ab4dbb20f2ae13a2babf00019f4ed93a6e9bf','bridge receipt');base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==11 and base['rows'][10]['module']=='Sign17DegreeCompose','bridge state')
need(sha(D/'research/nine-sharing-sign17-degree-staged-retry-check/attempt01/outer-result.json')=='6dd071e2a1c0b983f03c8dcc0cb28f98a5c507ee10395477a548a48a613eda16','bridge outer record')
need(sha(D/'reviews/nine-sharing-sign17-degree-staged-retry-terminal-independent/check.py')=='0510b85b20108976a1cdf627bb9f0cf97f044c033eec83997f541eda46d4399a','bridge terminal audit checker')
need(json.loads((D/'research/nine-sharing-sign17-degree-staged-retry-check/attempt01/outer-result.json').read_text())['outer_exit_code']==0,'shape outer status')
need(sha(P/'source-manifest.json')=='1247d4853085f2dbe5a74e42e9b38f5a5d9bf9eeece37a785e8c0511d7b9c836','manifest pin');manifest=json.loads((P/'source-manifest.json').read_text());entries=manifest['rows'];names=[x['module'].split('.')[-1] for x in entries];pins=[x['source_sha256'] for x in entries]
prior_state_path=D/'research/nine-sharing-sign17-univariate-degree-probe-retry02-check/attempt01/state.json'
prior_outer=D/'research/nine-sharing-sign17-univariate-degree-probe-retry02-check/attempt01/outer-result.json'
need(sha(prior_state_path)=='6f2b2ff507714a0c4d8f017292c12131e6523838d9518b7336468486c7a99038','univariate state')
need(sha(prior_outer)=='f3e9611ddbc09841ec54ca39390e78463dd1f5f00235cd56a9cb2509f4ad4ea4' and json.loads(prior_outer.read_text())['outer_exit_code']==0,'univariate outer')
need(sha(D/'reviews/nine-sharing-sign17-univariate-degree-probe-retry02-terminal-independent/check.py')=='0608299be3e408148c4f56ffe3c05b074798792377bfafffd783c1ca30e8ce53','univariate terminal audit')
prior=json.loads(prior_state_path.read_text());need(prior['status']=='PASS' and len(prior['rows'])==1 and prior['rows'][0]['source_sha256']==entries[0]['source_sha256'],'univariate source binding')
axis_state_path=D/'research/nine-sharing-sign17-axis-degree-base-retry-check/attempt01/state.json'
axis_outer=D/'research/nine-sharing-sign17-axis-degree-base-retry-check/attempt01/outer-result.json'
need(sha(axis_state_path)=='a167ca0d652e1f309ebe901d655e14f5924f75de7811d42af2e585edfca5381c','axis base state')
need(sha(axis_outer)=='9afdc9a05cff6104b617c9c17392e7e8946299cca8fc784f71462ad1fff83fa1' and json.loads(axis_outer.read_text())['outer_exit_code']==0,'axis base outer')
need(sha(D/'reviews/nine-sharing-sign17-axis-degree-base-retry-terminal-independent/check.py')=='c373ed00f7a31cba52daec677ecf305bab35fcbe48261a0ff591e817e045ffef','axis base audit')
axis=json.loads(axis_state_path.read_text());need(axis['status']=='PASS' and len(axis['rows'])==2 and all(axis['rows'][i]['source_sha256']==entries[i]['source_sha256'] for i in range(2)),'axis base source binding')
root_state_path=D/'research/nine-sharing-sign17-axis-degree-root-check/attempt01/state.json'
root_outer=D/'research/nine-sharing-sign17-axis-degree-root-check/attempt01/outer-result.json'
need(sha(root_state_path)=='8d14be59266cb5f0e8fbe0a0b401738fdf7116f4947295bfb2535d877801669c','root state')
need(sha(root_outer)=='24fe6ac4b687667e2e6e059af230334270eec37c37bfb0b1450f7b91e63e372b' and json.loads(root_outer.read_text())['outer_exit_code']==0,'root outer')
need(sha(D/'reviews/nine-sharing-sign17-axis-degree-root-terminal-independent/check.py')=='c1e57e40f4c7626f45f63b8c0917452df1927968f60e06965c1b5b034839bc21','root audit')
root=json.loads(root_state_path.read_text());need(root['status']=='PASS' and len(root['rows'])==3 and all(root['rows'][i]['source_sha256']==entries[i]['source_sha256'] for i in range(3)),'root source binding')
scale_state_path=D/'research/nine-sharing-sign17-axis-degree-scale-check/attempt01/state.json'
scale_outer=D/'research/nine-sharing-sign17-axis-degree-scale-check/attempt01/outer-result.json'
need(sha(scale_state_path)=='8146b0cca8b83e993b299df7622ec3a7726c8b5b1691cf261f1900f43e867a46','scale state')
need(sha(scale_outer)=='af9a1b4a145914b2429e3b769ab6a54c870b80cfb3f0c209fd3312f137c49dc9' and json.loads(scale_outer.read_text())['outer_exit_code']==0,'scale outer')
need(sha(D/'reviews/nine-sharing-sign17-axis-degree-scale-terminal-independent/check.py')=='3658632adea9397d9495fd66aac932e40f46368f3a5a5e53ea258626ccad5741','scale audit')
scale=json.loads(scale_state_path.read_text());need(scale['status']=='PASS' and len(scale['rows'])==4 and all(scale['rows'][i]['source_sha256']==entries[i]['source_sha256'] for i in range(4)),'scale source binding')
binding_state_path=D/'research/nine-sharing-sign17-axis-root-binding-staged-retry-check/attempt01/state.json'
binding_outer=D/'research/nine-sharing-sign17-axis-root-binding-staged-retry-check/attempt01/outer-result.json'
need(sha(binding_state_path)=='1119c131eee655a2592a321c8339645c4474bdb297c6529d82b2b4c6fe53d6e0','binding state')
need(sha(binding_outer)=='2c6cbcd7fa8b0c2b81ebc0202bf21dea8c9329774fff566099c949c4e39eee58' and json.loads(binding_outer.read_text())['outer_exit_code']==0,'binding outer')
need(sha(D/'reviews/nine-sharing-sign17-axis-root-binding-staged-retry-terminal-independent/check.py')=='2c7f04546de5c9537d84e382ff9697f537ab7ce2f744588af7cbf3141b3c4ed3','binding audit')
binding=json.loads(binding_state_path.read_text());need(binding['status']=='PASS' and len(binding['rows'])==7 and all(binding['rows'][i]['source_sha256']==entries[i]['source_sha256'] for i in range(7)),'binding source binding')
na_state_path=D/'research/nine-sharing-sign17-axis-na-degree-check/attempt01/state.json'
na_outer=D/'research/nine-sharing-sign17-axis-na-degree-check/attempt01/outer-result.json'
need(sha(na_state_path)=='42a5fcba409a7a2feb57a37109cc6dca655c9d1e4223df279224a9a7739f559d','na state')
need(sha(na_outer)=='4b35718a712fa1ab304430e9b935385e39d1b25a454f99d587c9ef926f4b7bd1' and json.loads(na_outer.read_text())['outer_exit_code']==0,'na outer')
need(sha(D/'reviews/nine-sharing-sign17-axis-na-degree-terminal-independent/check.py')=='379257743aeeeb76bb9419defe5f0816e24387d0527cc19283f92f41383c69ae','na audit')
na=json.loads(na_state_path.read_text());need(na['status']=='PASS' and len(na['rows'])==8 and all(na['rows'][i]['source_sha256']==entries[i]['source_sha256'] for i in range(8)),'na source binding')
other_state_path=D/'research/nine-sharing-sign17-axis-other-degree-check/attempt01/state.json'
other_outer=D/'research/nine-sharing-sign17-axis-other-degree-check/attempt01/outer-result.json'
need(sha(other_state_path)=='7461e6e2c7554b729b5e810e4019e83ebf79602466bafaaaee908225f5e21e9e','other state')
need(sha(other_outer)=='8d2f3f19381d57479db5ad76e10d77381cfc2f679c66559e38ce9ef599838ad2' and json.loads(other_outer.read_text())['outer_exit_code']==0,'other outer')
need(sha(D/'reviews/nine-sharing-sign17-axis-other-degree-terminal-independent/check.py')=='166370a2365c508982d4897bca8850169a7b3f85e2a9ff9ee15958bce9ea4694','other audit')
other=json.loads(other_state_path.read_text());need(other['status']=='PASS' and len(other['rows'])==9 and all(other['rows'][i]['source_sha256']==entries[i]['source_sha256'] for i in range(9)),'other source binding')
nc_state_path=D/'research/nine-sharing-sign17-axis-noncancel-check/attempt01/state.json'
nc_outer=D/'research/nine-sharing-sign17-axis-noncancel-check/attempt01/outer-result.json'
need(sha(nc_state_path)=='6716a653df6eb7affe2a97a57afaabd241343e36f503f57ae39ea6c2e51b86ac','noncancel state')
need(sha(nc_outer)=='8025d34fd9f518265869245fdc5ea46805ad66d5701df8bd84c17af7ab8b31d7' and json.loads(nc_outer.read_text())['outer_exit_code']==0,'noncancel outer')
need(sha(D/'reviews/nine-sharing-sign17-axis-noncancel-terminal-independent/check.py')=='1beb9e7152d856dad4277650bccd3ef1dc3b9827355ae434d81db8446e784caf','noncancel audit')
nc=json.loads(nc_state_path.read_text());need(nc['status']=='PASS' and len(nc['rows'])==10 and all(nc['rows'][i]['source_sha256']==entries[i]['source_sha256'] for i in range(10)),'noncancel source binding')
seed_state_path=D/'research/nine-sharing-sign17-axis-seed-degree-check/attempt01/state.json'
seed_outer=D/'research/nine-sharing-sign17-axis-seed-degree-check/attempt01/outer-result.json'
need(sha(seed_state_path)=='7d54a91eb7b6a913cb012fc873e98146f0cdc37dec93e420269acc47c5177669','seed state')
need(sha(seed_outer)=='d6c595a18c41da1a5320514b1a401114b77e8118c405dd2504b54e611198ea2c' and json.loads(seed_outer.read_text())['outer_exit_code']==0,'seed outer')
need(sha(D/'reviews/nine-sharing-sign17-axis-seed-degree-terminal-independent/check.py')=='292f7fdc5f0c7cb51fb33f45dc7631f8f86bee8130eee93fa94aaa7fe8b241a5','seed audit')
seed=json.loads(seed_state_path.read_text());need(seed['status']=='PASS' and len(seed['rows'])==11 and all(seed['rows'][i]['source_sha256']==entries[i]['source_sha256'] for i in range(11)),'seed source binding')
for row in base['rows']:
 n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0,'bridge stage '+n);need(sha(BASE/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(BASE/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'bridge source/object '+n)
 for key in ('deps','compile'):need(sha(BASE/(n+'-'+key+'.txt'))==row[key]['log_sha256'],'bridge log '+n)
 for k,v in row['direct_guard'].items():
  q=Path(k)
  if v is None:need(not os.path.lexists(q),'bridge unexpected '+k)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'bridge guard '+k)
for k,v in base['overlay_links'].items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'bridge overlay '+k)

for n in ('Sign17UnivariateDegreeProbe','Sign17AxisDegreeBase','Sign17AxisDegreeRoot','Sign17AxisDegreeScale','Sign17AxisBindingBase','Sign17AxisBindingFactors','Sign17AxisBindingRoot','Sign17AxisNaDegree','Sign17AxisOtherDegree','Sign17AxisNoncancel','Sign17AxisSeedDegree','Sign17AxisDiagonalDegree','Sign17AxisDiagonalBinding','Sign17AxisDegreeLower'):need(not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean')),'candidate target collision '+n)
need(sha(PKG/'Mathlib/Algebra/MvPolynomial/Equiv.olean')=='fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f','explicit domain module pin')
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
state={'status':'RUNNING','scope':'Bounded sign17 univariate degree probe using audited staged upper provider on captured Jones provider; no new base rebuild, no project-wide dependency load trace; endpoint outcome depends on stage results. Sampled monitor may miss transient spikes or escaped descendants.','base_state_sha256':sha(STATE),'runner_sha256':sha(__file__),'overlay_links':links,'rows':[]};save()
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
   if local=='Sign17DegreeCompose':expected_hash=base['rows'][10]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign17DegreeCompose.olean'
   elif local in ('Sign17UnivariateDegreeProbe','Sign17AxisDegreeBase','Sign17AxisDegreeRoot','Sign17AxisDegreeScale','Sign17AxisBindingBase','Sign17AxisBindingFactors','Sign17AxisBindingRoot','Sign17AxisNaDegree','Sign17AxisOtherDegree','Sign17AxisNoncancel','Sign17AxisSeedDegree','Sign17AxisDiagonalDegree','Sign17AxisDiagonalBinding','Sign20DirectNoAliasNative','Sign20DirectNoAliasStandard'):
    prior=[r for r in state['rows'][:-1] if r['module']==local];need(len(prior)==1,'local producer '+local);expected_hash=prior[0]['object_sha256'];path=OUT/'lib/DiophantineConsistency'/(local+'.olean')
   elif mod=='Mathlib.Algebra.MvPolynomial.Equiv':expected_hash='fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f';path=PKG/'Mathlib/Algebra/MvPolynomial/Equiv.olean'
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
 state['status']='PASS';save();print('PASS sign17 univariate degree probe')
except BaseException as e:
 state['status']='FAILED';state['failure']=repr(e);save();print('FAILED',repr(e));raise
