#!/usr/bin/env python3
"""Bounded order-block client against the audited single-context Fin942 provider."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file())
BASE=Path('/tmp/current14-carrier65-diagonal-whole-20261110');OUT=Path('/tmp/current14-carrier65-degree-direct-20261110')
SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py'
STATE=D/'research/current14-carrier65-diagonal-whole-check/attempt01/state.json';OUTER=STATE.parent/'outer-result.json';AUDIT=D/'reviews/current14-carrier65-diagonal-whole-terminal-independent/check.py'
roots=[OUT/'lib',SPHERE,MODEL,PKG,TOOL];suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,msg):
 if not x:raise RuntimeError(msg)
def guard(modules):
 ret={}
 for n in modules:
  for r in roots:
   for suf in suffixes:
    p=r/(n.replace('.','/')+suf)
    if os.path.lexists(p):need(p.is_file(),'bad candidate '+str(p));ret[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
    else:ret[str(p)]=None
 return ret
def save():
 t=OUT/'state.tmp';t.write_text(json.dumps(state,sort_keys=True,indent=2)+'\n');os.replace(t,OUT/'state.json')
need(not OUT.exists(),'output exists');need(sha(MON)=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad','monitor pin')
need(sha(STATE)=='d40d9ecec6acf598f85ea50977c85ba94827839074d3d6ec96152264c3ecd313','provider state pin')
need(sha(OUTER)=='764a9056c70ca2c3b716a0bc3ec2289abdbf24a84539e6b3a5c61d579a99ca2b' and json.loads(OUTER.read_text())['outer_exit_code']==0,'provider outer pin')
need(sha(AUDIT)=='8c749a9ecbb1132dedd167e3942d09c9a9bd582428dd5082322300c825380449','provider audit pin')
base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==3 and base['rows'][-1]['module']=='Current14Carrier65DiagonalWhole','provider status')
provider_init=base['rows'][0]['dependencies']['Init'];need(all(r['dependencies'].get('Init')==provider_init for r in base['rows']),'provider Init consistency')
need(provider_init['realpath']==str((TOOL/'Init.olean').resolve()) and provider_init['sha256']=='d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e','provider Init pin')
for row in base['rows']:
 n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0,'provider stage '+n)
 need(sha(BASE/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(BASE/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'provider source/object '+n)
 for key in ('deps','compile'):need(sha(BASE/(n+'-'+key+'.txt'))==row[key]['log_sha256'],'provider log '+n)
 for k,v in row['direct_guard'].items():
  q=Path(k)
  if v is None:need(not os.path.lexists(q),'provider unexpected '+k)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'provider guard '+k)
for k,v in base['overlay_links'].items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'provider overlay '+k)
need(sha(P/'source-manifest.json')=='bec2a0f9e8185986de8048485755d3b245aa572ff97ff203234bf6ff1d2c584e','manifest pin')
entries=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(entries)==2,'stage count');names=[e['module'].split('.')[-1] for e in entries];need(len(names)==len(set(names)),'duplicate names')
input_failure=D/'research/current14-carrier65-q-inputs-check/attempt01/state.json'
input_failure_outer=input_failure.parent/'outer-result.json'
input_failure_audit=D/'reviews/current14-carrier65-q-inputs-failure-independent/check.py'
need(sha(input_failure)=='2099b31cec0da9681e691a05caca84c43358a123c27effec3ee7995dd5312ad6' and json.loads(input_failure.read_text())['status']=='FAILED','input prior failure')
need(sha(input_failure_outer)=='3df782460615030e9ea3b9daac36b2617e8342f91b60fa2881ba458633f8e7de' and json.loads(input_failure_outer.read_text())['outer_exit_code']==1,'input prior outer')
need(sha(input_failure_audit)=='9b9a92f374b7eeee996cbd82f46ac9a0372cd2e53c2a028983a24910a18160d5','input failure audit')
replay_sources=[('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-degree-upper-draft/Current14Carrier65DegreeUpper.lean', '3cd57f38757f61f340b0e41829c7c869d507f2dd1c8e5c127c8bb122541713a2'), ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-degree-direct-draft/Current14Carrier65DegreeDirect.lean', '77fa0183832b7401d7af2f1c9cc38d2ff2eddcc646c8c069f6065e10b3e32244')]
for i,(path,digest) in enumerate(replay_sources):
 need(sha(path)==digest and sha(P/'src/DiophantineConsistency'/Path(path).name)==digest,'replay source '+str(i))
upper_state=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-degree-upper-check/attempt01/state.json');upper_outer=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-degree-upper-check/attempt01/outer-result.json');upper_audit=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews/current14-carrier65-degree-upper-terminal-independent/check.py')
upper=json.loads(upper_state.read_text())
need(sha(upper_state)=='7792f7ee03b7451cc8804e6280cd1843cc80c905e588c8359e16489472a1ace2' and upper['status']=='PASS','upper provider state')
need(len([r for r in upper['rows'] if r['source_sha256']==replay_sources[0][1] and r['compile']['exit']==0])==1,'audited upper replay source')
need(sha(upper_outer)=='cf45cc37853ea05a6d868f2ae256d8675567ae9985116c3e1ea527392a515241' and json.loads(upper_outer.read_text())['outer_exit_code']==0,'upper provider outer')
need(sha(upper_audit)=='018cb164406dbb1aac8b7fb3d2dd4a8aecf449770309123a43eaad11eb68bcd1','upper terminal audit')
for state_path,outer_path,audit_path,state_hash,outer_hash,audit_hash in [('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-degree-exact-check/attempt01/state.json', '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-degree-exact-check/attempt01/outer-result.json', '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews/current14-carrier65-degree-exact-failure-independent/check.py', 'f75adbea9e1b1343e7191a2d8a9941e2419bf48a7a1508e91e14bf78483463d7', '62071d3ab507f7dc4179c69b2e18c3c868cf0a994f49f4804be58662271e4d3c', '1b7df72196400d3f1c9fcc562dac13e10a7e167c2b92f76378aa84f0d500136d'), ('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-degree-exact-retry-check/attempt01/state.json', '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-degree-exact-retry-check/attempt01/outer-result.json', '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews/current14-carrier65-degree-exact-retry-failure-independent/check.py', '28ca083ca6e31aa53b0cd89b4eb00f6349eb2a68f90ee34b05754364bf656116', '3c256a58dfb97a821b27cb2a54ca3f8676cbc948d7a59e884bd2470d69d68e15', '59b533fb03fbb63e5610bca70be31b74349ba3633c9ce51759a79a2da1da2c0a')]:
 need(sha(state_path)==state_hash and json.loads(Path(state_path).read_text())['status']=='FAILED','prior failed state')
 need(sha(outer_path)==outer_hash and json.loads(Path(outer_path).read_text())['outer_exit_code']==1,'prior failed outer')
 need(sha(audit_path)==audit_hash,'prior failed audit')
extra_pins={'DiophantineConsistency.Current14Carrier65OtherFields': {'realpath': '/tmp/current14-carrier65-other-fields-20261110/lib/DiophantineConsistency/Current14Carrier65OtherFields.olean', 'sha256': 'a9a7ee626a02618960dc2b25bc72b2fbcbbb3af312f8da0d5fa31f0b28756d69'}, 'DiophantineConsistency.Current14Carrier65QActual': {'realpath': '/tmp/current14-carrier65-q-actual-retry-20261110/lib/DiophantineConsistency/Current14Carrier65QActual.olean', 'sha256': 'e8cf96d1efa522b6e6be8e219974fd3e6a4dd4b0796d2e27b7bc81e462f9b785'}, 'DiophantineConsistency.Current14Carrier65DiagonalDegree': {'realpath': '/tmp/current14-carrier65-diagonal-rank-20261110/lib/DiophantineConsistency/Current14Carrier65DiagonalDegree.olean', 'sha256': 'f2746903b163c21a444047539cc13f21a70cca9b942d0ee20fff69db124526cb'}}
diag_state=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-diagonal-degree-retry02-check/attempt01/state.json');diag_audit=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews/current14-carrier65-diagonal-degree-retry02-terminal-independent/check.py');diag=json.loads(diag_state.read_text())
need(sha(diag_state)=='1aab26b3648b4464f7653118f23febba8dc20a0dfd921b288e74410588957201' and diag['status']=='PASS' and sha(diag_audit)=='a6dd25fbe8cfdbffd0fccf7b379f886e64bdf796a9d82d34164be474bff42f8a','diagonal transport audit')
matching=[r for r in diag['rows'] if r['module']=='Current14Carrier65DiagonalDegree' and r['compile']['exit']==0]
need(len(matching)==1 and matching[0]['object_sha256']==extra_pins['DiophantineConsistency.Current14Carrier65DiagonalDegree']['sha256'],'diagonal equal-byte point')
for mod,rec in extra_pins.items():
 path=BASE/'lib'/(mod.replace('.','/')+'.olean')
 need(path.is_file() and str(path.resolve())==rec['realpath'] and sha(path)==rec['sha256'],'ingredient point '+mod)
provider_names={r['module']:r for r in base['rows']}
for e in entries:
 n=e['module'].split('.')[-1];src=P/'src/DiophantineConsistency'/(n+'.lean');need(sha(src)==e['source_sha256'] and sha(REPO/e['source'])==e['source_sha256'],'source pin '+n)
 need(not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean')),'provider collision '+n)
 need(re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'],'imports '+n)
 for m in e['imports']:need(m in extra_pins or m.split('.')[-1] in provider_names or m.split('.')[-1] in names[:names.index(n)],'unexpected provider import '+m)
if sys.argv[1:]==['--preflight']:
 print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','stage_count':len(entries),'scope':'Point-pinned Carrier65 ingredient; no Lean theorem or complete transitive import trace.'},sort_keys=True));raise SystemExit(0)
need(not sys.argv[1:],'unexpected arguments')
for proc in Path('/proc').iterdir():
 if not proc.name.isdecimal():continue
 try:need(not ((proc/'comm').read_text().strip()=='lean' and (proc/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X')),'another Lean process is active')
 except (FileNotFoundError,ProcessLookupError):continue
need(shutil.disk_usage('/tmp').free>=5_000_000_000 and int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024>=10*1024**3,'resources')
spec=importlib.util.spec_from_file_location('monitor',MON);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
OUT.mkdir();(OUT/'src/DiophantineConsistency').mkdir(parents=True);(OUT/'lib/DiophantineConsistency').mkdir(parents=True);links={}
for k,v in base['overlay_links'].items():
 rel=Path(k).relative_to(BASE/'lib');q=OUT/'lib'/rel;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(v);links[str(q)]=v
for n,row in provider_names.items():
 q=OUT/'lib/DiophantineConsistency'/(n+'.olean');need(not os.path.lexists(q),'overlay collision '+n);q.symlink_to((BASE/'lib/DiophantineConsistency'/(n+'.olean')).resolve());links[str(q)]=str(q.resolve())
for n in names:shutil.copyfile(P/'src/DiophantineConsistency'/(n+'.lean'),OUT/'src/DiophantineConsistency'/(n+'.lean'))
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,roots[:-1]));env['LEAN_NUM_THREADS']='1';state={'status':'RUNNING','rows':[],'overlay_links':links,'provider_state_sha256':sha(STATE),'manifest_sha256':sha(P/'source-manifest.json')};save()
try:
 for entry,n in zip(entries,names):
  src=OUT/'src/DiophantineConsistency'/(n+'.lean');need(sha(src)==entry['source_sha256'],'snapshot drift '+n)
  prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M3600','-j1','-DElab.async=false'];row={'module':n,'source_sha256':entry['source_sha256']};state['rows'].append(row);save()
  log=OUT/(n+'-deps.txt');res=monitor.run(prefix+['--deps',str(src)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['deps']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'deps failed '+n)
  deps={};counts={}
  for line in log.read_text().splitlines():
   p=Path(line);hits=[r for r in roots if p.is_relative_to(r)];need(p.is_absolute() and p.is_file() and line.endswith('.olean') and len(hits)==1,'bad dep '+line);mod=str(p.relative_to(hits[0]))[:-6].replace('/','.');counts[mod]=counts.get(mod,0)+1;need(mod not in deps or (mod=='Init' and counts[mod]<=2 and deps[mod]['path']==line),'duplicate '+mod);deps[mod]={'path':line,'realpath':str(p.resolve()),'sha256':sha(p)}
  need('Init' in deps,'implicit Init dependency '+n)
  need(set(deps)-{'Init'}==set(entry['imports'])-{'Init'},'dependency set '+n)
  for mod,rec in deps.items():
   candidates=[r/(mod.replace('.','/')+'.olean') for r in roots if (r/(mod.replace('.','/')+'.olean')).is_file()]
   need(candidates and str(candidates[0])==rec['path'],'first-candidate route '+mod)
   if mod=='Init':
    need(rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256'],'provider Init binding');continue
   depname=mod.split('.')[-1]
   if mod in extra_pins:expected=extra_pins[mod]['sha256'];path=Path(extra_pins[mod]['realpath'])
   elif depname in provider_names:expected=provider_names[depname]['object_sha256'];path=BASE/'lib/DiophantineConsistency'/(depname+'.olean')
   else:
    prior=[x for x in state['rows'][:-1] if x['module']==depname];need(len(prior)==1,'local producer '+depname);expected=prior[0]['object_sha256'];path=OUT/'lib/DiophantineConsistency'/(depname+'.olean')
   need(rec['sha256']==expected and rec['realpath']==str(path.resolve()),'direct producer '+mod)
  row['dependencies']=deps;row['direct_guard']=guard(deps);save();log=OUT/(n+'-compile.txt');obj=OUT/'lib/DiophantineConsistency'/(n+'.olean')
  res=monitor.run(prefix+['--root='+str(OUT/'src'),str(src),'-o',str(obj)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['compile']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'compile failed '+n)
  need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",log.read_text()) and obj.is_file(),'errors '+n);need(guard(deps)==row['direct_guard'],'guard drift '+n);row['object_sha256']=sha(obj);save()
 for entry,row in zip(entries,state['rows']):
  need(sha(OUT/'lib/DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'] and guard(row['dependencies'])==row['direct_guard'],'final drift '+row['module'])
 for k,v in links.items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'final overlay '+k)
 state['status']='PASS';save();print('PASS direct conditional exact polynomial degree')
except BaseException as e:
 state['status']='FAILED';state['exception']=repr(e);save();raise
