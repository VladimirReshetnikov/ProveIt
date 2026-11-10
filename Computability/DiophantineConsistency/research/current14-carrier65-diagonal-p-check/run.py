#!/usr/bin/env python3
"""Bounded order-block client against the audited single-context Fin942 provider."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file())
BASE=Path('/tmp/current14-carrier65-diagonal-rank-20261110');OUT=Path('/tmp/current14-carrier65-diagonal-p-20261110')
SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py'
STATE=D/'research/current14-carrier65-diagonal-rank-check/attempt01/state.json';OUTER=STATE.parent/'outer-result.json';AUDIT=D/'reviews/current14-carrier65-diagonal-rank-terminal-independent/check.py'
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
need(sha(STATE)=='e0d85b5d570c3437dd481e2ad502a403ebfcae44523186d72fc2b21f0d12823b','provider state pin')
need(sha(OUTER)=='d9186fbb7540d5552329f9e8d8270022a56533af1bbf9c99c5b3da49c52a3e67' and json.loads(OUTER.read_text())['outer_exit_code']==0,'provider outer pin')
need(sha(AUDIT)=='047c0ac0292981572f8358dd359569f6dfa95844f2543ae77d36eac7f293389a','provider audit pin')
base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==2 and base['rows'][-1]['module']=='Current14Carrier65DiagonalRank','provider status')
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
need(sha(P/'source-manifest.json')=='c17a764cccc164012aaa45a3008cbcc03f18c689774a5f8c3647b2550d73a2f0','manifest pin')
entries=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(entries)==1,'stage count');names=[e['module'].split('.')[-1] for e in entries];need(len(names)==len(set(names)),'duplicate names')
draft=D/'research/current14-carrier65-diagonal-p-draft/Current14Carrier65DiagonalP.lean'
need(sha(draft)=='31dd0d5db53a9790661e32d4d526f68c2edf336f524f75412ebf2b238fd2bd01' and sha(P/'src/DiophantineConsistency/Current14Carrier65DiagonalP.lean')==sha(draft),'P source pin')
BASE2=Path('/tmp/current14-carrier65-diagonal-core-binding-retry-20261110')
STATE2=D/'research/current14-carrier65-diagonal-core-binding-retry-check/attempt01/state.json';OUTER2=STATE2.parent/'outer-result.json'
need(sha(STATE2)=='898c4ee8f73d7f763586ba3cc3d4b63da8c8807838ec5df699d9c1b25c8d1f9f','second provider state')
need(sha(OUTER2)=='21a0e14ef818eb6e970a9f3aefa2c6bbdbccfd98132a77e52b32115bae817ad4' and json.loads(OUTER2.read_text())['outer_exit_code']==0,'second provider outer')
need(sha(D/'reviews/current14-carrier65-diagonal-core-binding-retry-terminal-independent/check.py')=='c1a3e74eaa5551b426dc162ad0bc08faf30f142d295006d25e16795fe757d26e','second provider audit')
base2=json.loads(STATE2.read_text());need(base2['status']=='PASS' and len(base2['rows'])==2 and base2['rows'][-1]['module']=='Current14Carrier65DiagonalCoreBinding','second provider status')
for row in base2['rows']:
 n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0,'second provider stage '+n)
 need(row['dependencies'].get('Init')==provider_init,'second Init '+n)
 need(sha(BASE2/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(BASE2/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'second source/object '+n)
 for key in ('deps','compile'):need(sha(BASE2/(n+'-'+key+'.txt'))==row[key]['log_sha256'],'second log '+n)
 for k,v in row['direct_guard'].items():
  q=Path(k)
  if v is None:need(not os.path.lexists(q),'second unexpected '+k)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'second guard '+k)
for k,v in base2['overlay_links'].items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'second overlay '+k)
def relmap(b,root):return {str(Path(k).relative_to(root/'lib')):v for k,v in b['overlay_links'].items()}
firstmap=relmap(base,BASE);secondmap=relmap(base2,BASE2);overlap=set(firstmap)&set(secondmap)
exception='DiophantineConsistency/Current14Carrier65QFields.olean'
need(len(overlap)==1267 and exception in overlap,'provider overlap size')
need(all(firstmap[k]==secondmap[k] for k in overlap if k!=exception),'provider overlay mismatch')
need(firstmap[exception]!=secondmap[exception] and sha(firstmap[exception])==sha(secondmap[exception])=='ffc15e09467d94f0f1c8752c38fbb06579d16b30863fb8954ef0950b5a568f0b','QFields equal-byte route exception')
provider2_names={r['module']:r for r in base2['rows']}
provider_names={r['module']:r for r in base['rows']}
for e in entries:
 n=e['module'].split('.')[-1];src=P/'src/DiophantineConsistency'/(n+'.lean');need(sha(src)==e['source_sha256'] and sha(REPO/e['source'])==e['source_sha256'],'source pin '+n)
 need(not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean')),'provider collision '+n)
 need(re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'],'imports '+n)
 for m in e['imports']:need(m.startswith('DiophantineConsistency.') and m.split('.')[-1] in (set(provider_names)|set(provider2_names)),'unexpected provider import '+m)
if sys.argv[1:]==['--preflight']:
 print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','stage_count':len(entries),'scope':'Two audited providers; one explicitly pinned equal-byte QFields path difference; no Lean theorem or complete transitive trace.'},sort_keys=True));raise SystemExit(0)
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
for rel,v in secondmap.items():
 q=OUT/'lib'/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if os.path.lexists(q):need(q.is_symlink() and (str(q.resolve())==v or (rel==exception and sha(q)==sha(v))),'union mismatch '+rel)
 else:q.symlink_to(v);links[str(q)]=v
for n,row in provider2_names.items():
 q=OUT/'lib/DiophantineConsistency'/(n+'.olean');target=(BASE2/'lib/DiophantineConsistency'/(n+'.olean')).resolve()
 if os.path.lexists(q):need(q.is_symlink() and q.resolve()==target,'second object collision '+n)
 else:q.symlink_to(target);links[str(q)]=str(target)
for n in names:shutil.copyfile(P/'src/DiophantineConsistency'/(n+'.lean'),OUT/'src/DiophantineConsistency'/(n+'.lean'))
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,roots[:-1]));env['LEAN_NUM_THREADS']='1';state={'status':'RUNNING','rows':[],'overlay_links':links,'provider_state_sha256':sha(STATE),'second_provider_state_sha256':sha(STATE2),'provider_overlap_count':len(overlap),'manifest_sha256':sha(P/'source-manifest.json')};save()
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
   depname=mod.split('.')[-1];is_second=depname in provider2_names;expected=(provider2_names if is_second else provider_names)[depname]['object_sha256'];path=(BASE2 if is_second else BASE)/'lib/DiophantineConsistency'/(depname+'.olean')
   need(rec['sha256']==expected and rec['realpath']==str(path.resolve()),'direct producer '+mod)
  row['dependencies']=deps;row['direct_guard']=guard(deps);save();log=OUT/(n+'-compile.txt');obj=OUT/'lib/DiophantineConsistency'/(n+'.olean')
  res=monitor.run(prefix+['--root='+str(OUT/'src'),str(src),'-o',str(obj)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['compile']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'compile failed '+n)
  need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",log.read_text()) and obj.is_file(),'errors '+n);need(guard(deps)==row['direct_guard'],'guard drift '+n);row['object_sha256']=sha(obj);save()
 for entry,row in zip(entries,state['rows']):
  need(sha(OUT/'lib/DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'] and guard(row['dependencies'])==row['direct_guard'],'final drift '+row['module'])
 for k,v in links.items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'final overlay '+k)
 state['status']='PASS';save();print('PASS actual diagonal P degree')
except BaseException as e:
 state['status']='FAILED';state['exception']=repr(e);save();raise
