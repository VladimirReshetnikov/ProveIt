#!/usr/bin/env python3
"""Bounded, source-pinned experiment; inherits 13-variable provider ancestry."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file());BASE=Path('/tmp/nine-sharing-sign14-positive74-object-shift-matrix-check-20261110');OUT=Path('/tmp/nine-sharing-sign14-positive74-object-succ-guard-check-20261110');SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py';STATE=D/'research/nine-sharing-sign14-positive74-object-shift-matrix-check/attempt01/state.json';roots=[OUT/'lib',SPHERE,MODEL,PKG,TOOL];suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']
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
 need(sha(P/'framework-survey.py')=='42f3341a4663fc4ef801c54c8dcad56f0a76cf31d193bc4e51cc0c3378bcb9c2','framework survey pin')
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'framework-survey.py')],capture_output=True,timeout=120);need(r.returncode==0 and not r.stderr,'framework survey');framework=json.loads(r.stdout);need(framework['status']=='PASS','framework status')
check_external_syntax()
need(sha(D/'research/nine-sharing-sign26-endpoint-retry01/attempt01/state.json')=='8b7490adbdecd01e9d23d3a8978c72d38deb5ef97d931ca1120627acdf2d7003','retry failure receipt')
need(sha(D/'research/nine-sharing-sign14-positive74-object-predecessor-check/attempt01/state.json')=='a998206e3553cacca599b3f05f39d1cfc4e0e734ae2da9d56c2f626a2a1a15fb','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-predecessor-check/attempt01/outer-result.json')=='cd6a5e6384c7ed02d95bad47ea420b9548fafb81004a4a4923d278ae14e743c6','prior failure audit pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-predecessor-failure-independent/check.py')=='1a8f727cd68db1d37a1ff9fe2ffcec1bbb78622ac0ee4e9bc6ea7bd7ba9040f2','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-predecessor-retry01-check/attempt01/state.json')=='208216e9c414957fa839e9928a1534e113466ae4b6da573db3e5efd706cf7d86','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-predecessor-retry01-check/attempt01/outer-result.json')=='58e7f47315e6afaee566d07b813586d07c2bb2f71b2882af6d777155f15f81e9','prior failure audit pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-predecessor-retry01-failure-independent/check.py')=='331cf91656d968afc5af5c343bbe4c9c683e97d0b14899856ad37e5c2c2392cd','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-coordinate-elim-check/attempt01/state.json')=='59246dd49d26d247ad8ca250a1b56f37a8ca136c140d817fb20787729bb67800','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-coordinate-elim-check/attempt01/outer-result.json')=='ad9eba5beb6f8a7b8f7cf39aadd53a158690c3af1cbf853c7620016ff71cce50','prior failure audit pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-coordinate-elim-failure-independent/check.py')=='18cd672cd8df35e603971d33720708bdfd25472fe0ec6b88d2657064159330a5','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-coordinate-elim-retry01-check/attempt01/state.json')=='6ffbf67aa613cbd55287d339fe5e20bd1a41346afe6bf1c2d479a2b8ce811264','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-coordinate-elim-retry01-check/attempt01/outer-result.json')=='eed10d94346584e67f342db4e0dc2ba75729f81e868c367bebfac2d7f6bc3cd9','prior failure audit pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-coordinate-elim-retry01-failure-independent/check.py')=='942d29617ff071a5565395834a9c618d69317bf4eba0e17306c07df16c043f8f','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-coordinate-arrangement-check/attempt01/state.json')=='3bdffef7a3903de2b04d9ffc27b5fea91aa61dee05ae7440d4cbae3e35ab6045','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-coordinate-arrangement-check/attempt01/outer-result.json')=='08367f8388f7bfa6bfed7419078c2a4cb15372435486f4bab2328b33efb1c510','prior failure audit pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-coordinate-arrangement-failure-independent/check.py')=='2251661b16193fe6a08fd19474b471226295211cb9fbc9a559db804008470a25','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-multisubst-check/attempt01/state.json')=='e68f5b0d272866b67fd124bca667e6ed6d87b60e8517210dcc884f9f576a3a3f','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-multisubst-check/attempt01/outer-result.json')=='0624e62abdce13881ad281daebce08e44f4ade0b246bc2061ed74f7491d0e474','prior failure audit pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-multisubst-failure-independent/check.py')=='dc312d044a4d34c5c5cd6ee1502431e3b2c793dc00b2ee1c78b3db47a0411488','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-multisubst-retry01-check/attempt01/state.json')=='b876e4278acc71ad598ac738bf50f6f6aa4a523c349a39a91b9ef1deb65f5fbd','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-multisubst-retry01-check/attempt01/outer-result.json')=='1d1f7294b9136f63b56488a0964b74f45da54e1bf290986dffb5c94221baaed4','prior failure audit pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-multisubst-retry01-failure-independent/check.py')=='04f3d0b94fd62a65e315f512a6d07b730b2733437555446fab3ec55cd8f4aa25','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-multisubst-retry02-check/attempt01/state.json')=='bd77aa7982c0bfe083e9403780ce7f8007410d30938886bf6c66d1956f1c5986','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-multisubst-retry02-check/attempt01/outer-result.json')=='fa2d79d94bb8e6794f7961217b6d8c0a73d60dafb0e5874aa514c5c47ba2a1ac','prior failure audit pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-multisubst-retry02-failure-independent/check.py')=='5117ee0e956c5734de099ed2aaa3f4a206f7ad88a39ee0ea3ef40afec084784e','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-shift-base-check/attempt01/state.json')=='4ce470a805975eac7d3009fe516c46d36d2a5a3a21de4b52006ec62d8e0b2a40','prior failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-shift-base-check/attempt01/outer-result.json')=='78614632c7b5b164ec602b4bc1fcb01d617f07c66ea3200961c5de86ea208c8e','prior failure pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-shift-base-failure-independent/check.py')=='a341171fa2850c068af62107753d6a16f45fbb61ce42fd0deb890bbc672a2b53','prior failure audit pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-shift-base-retry01-check/attempt01/state.json')=='cc11bb7f4999cb7f4fead5715da9e58918d9a99a066ee13fcb57682f13d8d23c','prior retry failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-shift-base-retry01-check/attempt01/outer-result.json')=='303f06771c7d5bd4c19e62304a875f776c594c718627e5e7330835a51d363ce6','prior retry failure pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-shift-base-retry01-failure-independent/check.py')=='367a52d624d132f95ad9ec0dfa228ecdfb87b8d15bab48730f46f10afb9a715d','prior retry failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-function-binary-check/attempt01/state.json')=='d657829e23fd1ada77834f3ee0247dc441834156d452de3f230766c9bdb740de','prior binary failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-function-binary-check/attempt01/outer-result.json')=='f8d864bdfb003ddd81005d03b22f78fcd3658d152a40e68778207377b4fe7789','prior binary failure pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-function-binary-failure-independent/check.py')=='e8491bad8fd117e5a90116d771e6361f4fb9290c5de47841de69f87fb9d1102e','prior binary failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-compiler-ops-check/attempt01/state.json')=='587c9ad14ff23d6d521708f7c877499e731c6bda57d91bb7ee26ae4f13ce01bf','prior compiler failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-compiler-ops-check/attempt01/outer-result.json')=='29caaa51839132602784820f51c7e978c3c4ed9484fb0742a4a7eb22295df43e','prior compiler failure pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-compiler-ops-failure-independent/check.py')=='850ab020f460354e88a3e09b6561d4b8c7103954646bc0bad1694071ee0838a0','prior compiler failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-compiler-leaves-check/attempt01/state.json')=='0852e5347877a203f5a81706aa91a8b3be45887b26dc53abf777c99ec094ed32','prior compiler leaves failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-compiler-leaves-check/attempt01/outer-result.json')=='88e86e9fec46a6a51accb700e1c36c9b2b144b1063fa3567406f240aa8093928','prior compiler leaves failure pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-compiler-leaves-failure-independent/check.py')=='634c287bbcd43f1930c3046d0b126d9968ac1cfacb9d6d0063888494152a68fe','prior compiler leaves failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-compiler-constant-check/attempt01/state.json')=='1496181c0d80d51902db499bc774c0e149ee6b3843639e8be1d664cdeb24918a','prior constant failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-compiler-constant-check/attempt01/outer-result.json')=='eb1dafb6dfb73a9a11f7841424bb98f9338bb7dbcc9b71f5fb2bc92b33230132','prior constant failure pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-compiler-constant-failure-independent/check.py')=='35593ccdbf0ec68355ce00ffae8d273e8d3aee8b0b62a75ea180c591d4a0c3e3','prior constant failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-mul-zero-context-check/attempt01/state.json')=='409a3e4f5a31989f0c9057d1bfa4274c4c28eac836b63d3cd75b851e06ca5d73','prior mul-zero failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-mul-zero-context-check/attempt01/outer-result.json')=='1febd24841cef62ee232cff00f976baa2fa71653cd2b038abb77f9da099c336a','prior mul-zero failure pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-mul-zero-context-failure-independent/check.py')=='f12c140197ee7858dc2f811977a3efb07f70afe065d3b988d262ffb756c922b4','prior mul-zero failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-equality-transport-check/attempt01/state.json')=='1fabb48577c1f7733a0baa073a3b08fa2137feed34bbbd392dd99e2265d18d29','prior equality-transport failure pin')
need(sha(D/'research/nine-sharing-sign14-positive74-object-equality-transport-check/attempt01/outer-result.json')=='625e989f18dfa76d2a38dba49def943e956e185a5e208c96e7d4184fe1641bed','prior equality-transport failure pin')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-equality-transport-failure-independent/check.py')=='1211183f0c8e8490cae33f1e966cb0feb853291a1d361200a29b1a4577deb248','prior equality-transport failure pin')
need(not OUT.exists(),'output exists');need(sha(MON)=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad','monitor');need(sha(STATE)=='db986a6c989ff0f1229be1ac953c31b65b5728e960a48e4f0f99df1624174bb7','bridge receipt');base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==1 and base['rows'][0]['module']=='Sign14Positive74ObjectShiftMatrix','bridge state')
need(sha(D/'research/nine-sharing-sign14-positive74-object-shift-matrix-check/attempt01/outer-result.json')=='b785bdebe94fa11f4851f9b31d17a1eb35ace4ac4b0882e4dcf1e5be3d99aac3','bridge outer record')
need(sha(D/'reviews/nine-sharing-sign14-positive74-object-shift-matrix-terminal-independent/check.py')=='f0b9ae3b28837f26c1966819e314ba2f14be62a42e24e31152419b66b8ae89ee','bridge terminal audit checker')
need(json.loads((D/'research/nine-sharing-sign14-positive74-object-shift-matrix-check/attempt01/outer-result.json').read_text())['author_observed_numeric_outer_exit']==0,'bridge outer status')
need(sha(P/'source-manifest.json')=='a99cb39c7c1d012d7f91e2457337070f993460df9fd91c96654308c782764fb6','manifest pin');manifest=json.loads((P/'source-manifest.json').read_text());entries=manifest['rows'];names=[x['module'].split('.')[-1] for x in entries];pins=[x['source_sha256'] for x in entries]
for row in base['rows']:
 n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0,'bridge stage '+n);need(sha(BASE/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(BASE/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'bridge source/object '+n)
 for key in ('deps','compile'):need(sha(BASE/(n+'-'+key+'.txt'))==row[key]['log_sha256'],'bridge log '+n)
 for k,v in row['direct_guard'].items():
  q=Path(k)
  if v is None:need(not os.path.lexists(q),'bridge unexpected '+k)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'bridge guard '+k)
for k,v in base['overlay_links'].items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'bridge overlay '+k)

for n in ('Sign14Positive74ObjectSuccGuard',):need(not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean')),'candidate target collision '+n)
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
state={'status':'RUNNING','scope':'Bounded sign14 positive74 successor guard on captured Jones provider; no new base rebuild, no project-wide dependency load trace; endpoint outcome depends on stage results. Sampled monitor may miss transient spikes or escaped descendants.','base_state_sha256':sha(STATE),'runner_sha256':sha(__file__),'overlay_links':links,'rows':[]};save()
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
   if local=='Sign14Positive74ObjectShiftMatrix':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign14Positive74ObjectShiftMatrix.olean'
   elif local in ('Sign14SyntaxDegree','Sign14SharedDegree00','Sign14SharedDegree01','Sign14SharedDegree02','Sign14SharedDegree03','Sign14SharedDegree04','Sign14SharedDegree05','Sign14SharedDegree06','Sign14SharedDegree07','Sign14SharedDegree08','Sign14RowDegree00','Sign14RowDegree01','Sign14RowDegree02','Sign14RowDegree03','Sign14RowDegree04','Sign14DegreeStructural','Sign14DegreeResiduals'):
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
 state['status']='PASS';save();print('PASS sign14 positive74 successor guard')
except BaseException as e:
 state['status']='FAILED';state['failure']=repr(e);save();print('FAILED',repr(e));raise
