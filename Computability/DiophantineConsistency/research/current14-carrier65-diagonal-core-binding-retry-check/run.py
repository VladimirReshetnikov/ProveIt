#!/usr/bin/env python3
"""Bounded order-block client against the audited single-context Fin942 provider."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file())
BASE=Path('/tmp/current14-carrier65-diagonal-binding-20261110');OUT=Path('/tmp/current14-carrier65-diagonal-core-binding-retry-20261110')
SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py'
STATE=D/'research/current14-carrier65-diagonal-binding-check/attempt01/state.json';OUTER=STATE.parent/'outer-result.json';AUDIT=D/'reviews/current14-carrier65-diagonal-binding-terminal-independent/check.py'
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
need(sha(STATE)=='8acdc8a788e3619f0ba1d6ee820dad4ff1ae7232f731bf70d6da4c82c414507f','provider state pin')
need(sha(OUTER)=='82151e63e03b99294d7273edc64d7fda5784098f346d3a9ddd896a9088412a84' and json.loads(OUTER.read_text())['outer_exit_code']==0,'provider outer pin')
need(sha(AUDIT)=='d255a090ddab1cef80e5bd594d1ef74771b74bb91fe6f3337292fe0549b9183f','provider audit pin')
base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==1 and base['rows'][-1]['module']=='Current14Carrier65DiagonalBinding','provider status')
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
need(sha(P/'source-manifest.json')=='4b553d683d51c75e0323464d4fe380ea9cb8414705282fdf8d9be9d098b91c6a','manifest pin')
entries=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(entries)==2,'stage count');names=[e['module'].split('.')[-1] for e in entries];need(len(names)==len(set(names)),'duplicate names')
input_failure=D/'research/current14-carrier65-q-inputs-check/attempt01/state.json'
input_failure_outer=input_failure.parent/'outer-result.json'
input_failure_audit=D/'reviews/current14-carrier65-q-inputs-failure-independent/check.py'
need(sha(input_failure)=='2099b31cec0da9681e691a05caca84c43358a123c27effec3ee7995dd5312ad6' and json.loads(input_failure.read_text())['status']=='FAILED','input prior failure')
need(sha(input_failure_outer)=='3df782460615030e9ea3b9daac36b2617e8342f91b60fa2881ba458633f8e7de' and json.loads(input_failure_outer.read_text())['outer_exit_code']==1,'input prior outer')
need(sha(input_failure_audit)=='9b9a92f374b7eeee996cbd82f46ac9a0372cd2e53c2a028983a24910a18160d5','input failure audit')
failed_state=D/'research/current14-carrier65-diagonal-core-binding-check/attempt01/state.json'
failed_outer=failed_state.parent/'outer-result.json'
failed_audit=D/'reviews/current14-carrier65-diagonal-core-binding-failure-independent/check.py'
need(sha(failed_state)=='dad8a5f1ce55007cecb4c92765aac1841e2ff13cb4a33e6a5cd1fdd6eb127311' and json.loads(failed_state.read_text())['status']=='FAILED','diagonal core binding parent failure')
need(sha(failed_outer)=='540a571e97c7fdc20c218053ed82fdacd85718875be0cda0eb8fb37ac5ed3b2c' and json.loads(failed_outer.read_text())['outer_exit_code']==1,'diagonal core binding parent outer')
need(sha(failed_audit)=='7f1c952980845073d13b59258f2fcb0bf16f53bb9db078cbddd4a91924c6b2d2','diagonal core binding failure audit')
need(sha(Path('/tmp/current14-carrier65-diagonal-core-binding-20261110/Current14Carrier65DiagonalCoreBinding-compile.txt'))=='016fcc16afb0f1e295efeddb8dd350410758e77ac41c21c87f35aa9dfa8106cd','diagonal core binding failure log')
need(not Path('/tmp/current14-carrier65-diagonal-core-binding-20261110/lib/DiophantineConsistency/Current14Carrier65DiagonalCoreBinding.olean').exists(),'diagonal core binding parent object absent')
replay_source=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-diagonal-core-retry-draft/Current14Carrier65DiagonalCore.lean')
need(sha(replay_source)=='28f70e818c9b03e360d8bb0c30c166c5255b779037ec68f5026189b9e6b09311' and sha(P/'src/DiophantineConsistency/Current14Carrier65DiagonalCore.lean')==sha(replay_source),'audited Q-fields replay source')
need(sha(Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-diagonal-core-retry-check/attempt01/state.json'))=='df63f9b23013f3cfda8b5431daec85f260b3a1ec74e2839cdbceccae6fa8e08e','Q-fields replay state')
replay=json.loads(Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-diagonal-core-retry-check/attempt01/state.json').read_text())
need(replay['status']=='PASS' and len(replay['rows'])==1 and replay['rows'][0]['source_sha256']==sha(replay_source) and replay['rows'][0]['compile']['exit']==0,'Q-fields replay source and stage')
need(sha(Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-diagonal-core-retry-check/attempt01/outer-result.json'))=='10425495e32fa22ec96e46f817ec76826b8b1c423e04ba76c40ee4d215eb2b8d' and json.loads(Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-diagonal-core-retry-check/attempt01/outer-result.json').read_text())['outer_exit_code']==0,'Q-fields replay outer')
need(sha(Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews/current14-carrier65-diagonal-core-retry-terminal-independent/check.py'))=='3d3b69ce9fcb65c030489fbbcae78760e74eb7709cea222b27e2a4c4b640aa26','Q-fields replay audit')
draft=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current14-carrier65-diagonal-core-binding-retry-draft/Current14Carrier65DiagonalCoreBinding.lean')
need(sha(draft)=='0f12be5a6eeb2ed307fb7f5a6332964d0d69019ce6470bbb46f4341e78910cdc' and sha(P/'src/DiophantineConsistency/Current14Carrier65DiagonalCoreBinding.lean')==sha(draft),'other fields source')
extra_pins={'DiophantineConsistency.Current14Carrier65DiagonalBase': {'realpath': '/tmp/current14-carrier65-diagonal-base-retry-20261110/lib/DiophantineConsistency/Current14Carrier65DiagonalBase.olean', 'sha256': 'd7cf928584642bb7b58f9fa9f30cd5d7dee548aa8a6523aa9d3d2d254de2a4ff'}, 'DiophantineConsistency.Carrier65': {'realpath': '/tmp/normalized106-fresh-model-build-v2-20261105/lib/DiophantineConsistency/Carrier65.olean', 'sha256': '10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f'}}
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
 state['status']='PASS';save();print('PASS current14 diagonal core field binding')
except BaseException as e:
 state['status']='FAILED';state['exception']=repr(e);save();raise
