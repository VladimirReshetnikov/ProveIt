#!/usr/bin/env python3
"""Bounded three-stage Carrier65 DAG, count, and semantic-equality client."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file())
BASE=Path('/tmp/nine-sharing-sign17-readable-current14-endpoint-20261110');OUT=Path('/tmp/current14-carrier65-dag-check-20261110')
SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py'
STATE=D/'research/nine-sharing-sign17-readable-current14-endpoint-check/attempt01/state.json';OUTER=STATE.parent/'outer-result.json';AUDIT=D/'reviews/nine-sharing-sign17-readable-current14-endpoint-terminal-independent/check.py'
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
need(sha(STATE)=='ef0c59cff931294bdad43380d8f84a3bd27c178b26521b7b7b1513f8862ea213','provider state pin')
need(sha(OUTER)=='d566022ecfc42e5138fca689e08ee44b3bfca6522daf5ef6bfe62c9d70f7adf2' and json.loads(OUTER.read_text())['outer_exit_code']==0,'provider outer pin')
need(sha(AUDIT)=='3a764669d768d2ff0d4c12b921c2787dc8d752058d2041d5ca79ebb7ac6694a6','provider audit pin')
base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==1 and base['rows'][-1]['module']=='Sign17ReadableCurrent14Endpoint','provider status')
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
need(sha(P/'source-manifest.json')=='71d6f8cca595c5926048fdab1ecafaeec4ff964719b801b5960182187222b292','manifest pin')
entries=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(entries)==3,'stage count');names=[e['module'].split('.')[-1] for e in entries];need(len(names)==len(set(names)),'duplicate names')
draft=D/'research/current14-carrier65-dag-draft/Current14Carrier65DAG.lean'
need(sha(draft)=='3c4de94f1ddf593bd720d31d822182a1298da3db035f6f03c0707d5b587628da','reviewed draft pin')
need(sha(D/'reviews/current14-carrier65-dag-draft-independent/check.py')=='3f736b1ea8197a9580911e6a6ded271e37759b79ddfd4557c014647b1290d0c6','source audit pin')
need(sha(P/'src/DiophantineConsistency/ArithmeticDAG.lean')=='75fcb725f7a32287e58ccf70a10737c05f3c9ebfda152dbe2770e3bba12848d9','infrastructure source pin')
reviewed=draft.read_text();cut=reviewed.index('/-- This is the essential bridge')
core=(P/'src/DiophantineConsistency/Current14Carrier65DAGCore.lean').read_text()
value=(P/'src/DiophantineConsistency/Current14Carrier65DAGValue.lean').read_text()
need(core.startswith(reviewed[:cut].replace('import DiophantineConsistency.Carrier65\n','',1)),'core reviewed declarations')
need(reviewed[cut:reviewed.rindex('\nend DiophantineConsistency.Current14Carrier65DAG')] in value,'semantic reviewed declaration')
package_pins={'Mathlib.Algebra.MvPolynomial.Eval': {'realpath': '/home/codex/src/Proofs/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/MvPolynomial/Eval.olean', 'sha256': '7882f4461e9008365c09da94b86851730f78993275c5d7ccacb5b58baaf52d28'}, 'Mathlib.Data.List.GetD': {'realpath': '/home/codex/src/Proofs/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/List/GetD.olean', 'sha256': '9eb57c288a2cb78f8f745e0e2013c38a5763a39930c1e53cc23edb40e458598d'}, 'Mathlib.Logic.Relation': {'realpath': '/home/codex/src/Proofs/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Logic/Relation.olean', 'sha256': '22c635d2fb365291cab821653d3cc2a61eedb7dcf91cc52d623325794d0151c4'}, 'Mathlib.Tactic': {'realpath': '/home/codex/src/Proofs/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean', 'sha256': '55ee2345729e8a4d379de3bce14ea18b14fbfdc259cf2653fadf4bf3a46876d8'}}
carrier_pin={'realpath': '/tmp/normalized106-fresh-model-build-v2-20261105/lib/DiophantineConsistency/Carrier65.olean', 'sha256': '10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f'}
for mod,rec in package_pins.items():
 path=PKG/(mod.replace('.','/')+'.olean');need(path.is_file() and str(path.resolve())==rec['realpath'] and sha(path)==rec['sha256'],'package direct pin '+mod)
carrier=BASE/'lib/DiophantineConsistency/Carrier65.olean'
need(carrier.is_file() and str(carrier.resolve())==carrier_pin['realpath'] and sha(carrier)==carrier_pin['sha256'],'carrier direct pin')
provider_names={r['module']:r for r in base['rows']}
for e in entries:
 n=e['module'].split('.')[-1];src=P/'src/DiophantineConsistency'/(n+'.lean');need(sha(src)==e['source_sha256'] and sha(REPO/e['source'])==e['source_sha256'],'source pin '+n)
 need(not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean')),'provider collision '+n)
 need(re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'],'imports '+n)
 for m in e['imports']:need(m in package_pins or m=='DiophantineConsistency.Carrier65' or m.split('.')[-1] in names[:names.index(n)],'unexpected direct import '+m)
if sys.argv[1:]==['--preflight']:
 print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','stage_count':len(entries),'scope':'Audited provider and guarded staged sources; no Lean theorem or full transitive import trace.'},sort_keys=True));raise SystemExit(0)
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
   if mod in package_pins:
    expected=package_pins[mod]['sha256'];path=Path(package_pins[mod]['realpath'])
   elif mod=='DiophantineConsistency.Carrier65':
    expected=carrier_pin['sha256'];path=Path(carrier_pin['realpath'])
   else:
    prior=[x for x in state['rows'][:-1] if x['module']==depname];need(len(prior)==1,'local producer '+depname);expected=prior[0]['object_sha256'];path=OUT/'lib/DiophantineConsistency'/(depname+'.olean')
   need(rec['sha256']==expected and rec['realpath']==str(path.resolve()),'direct producer '+mod)
  row['dependencies']=deps;row['direct_guard']=guard(deps);save();log=OUT/(n+'-compile.txt');obj=OUT/'lib/DiophantineConsistency'/(n+'.olean')
  res=monitor.run(prefix+['--root='+str(OUT/'src'),str(src),'-o',str(obj)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['compile']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'compile failed '+n)
  need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",log.read_text()) and obj.is_file(),'errors '+n);need(guard(deps)==row['direct_guard'],'guard drift '+n);row['object_sha256']=sha(obj);save()
 for entry,row in zip(entries,state['rows']):
  need(sha(OUT/'lib/DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'] and guard(row['dependencies'])==row['direct_guard'],'final drift '+row['module'])
 for k,v in links.items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'final overlay '+k)
 state['status']='PASS';save();print('PASS current14 Carrier65 circuit and semantic bridge')
except BaseException as e:
 state['status']='FAILED';state['exception']=repr(e);save();raise
