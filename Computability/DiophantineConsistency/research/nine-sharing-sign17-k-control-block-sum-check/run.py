#!/usr/bin/env python3
"""Bounded order-block client against the audited single-context Fin942 provider."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];REPO=next(p for p in P.parents if (p/'lakefile.toml').is_file())
BASE=Path('/tmp/nine-sharing-sign17-k-ranked-rawword-retry-20261110');OUT=Path('/tmp/nine-sharing-sign17-k-control-block-sum-20261110')
SPHERE=Path('/tmp/current2011-spheres-fresh-base-priority-check02');MODEL=Path('/tmp/normalized106-fresh-model-client-20261105');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py'
STATE=D/'research/nine-sharing-sign17-k-ranked-rawword-retry-check/attempt01/state.json';OUTER=STATE.parent/'outer-result.json';AUDIT=D/'reviews/nine-sharing-sign17-k-ranked-rawword-retry-terminal-independent/check.py'
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
need(sha(STATE)=='8cadee9af856f69894ab2d7b6226b47a4205e498c50337b6ac2e02f5681f1218','provider state pin')
need(sha(OUTER)=='14f9faf6d8e1012f01f9b0d240e3cee0b89a6d1b80ab757fee10cbd4523d53c9' and json.loads(OUTER.read_text())['outer_exit_code']==0,'provider outer pin')
need(sha(AUDIT)=='4833bd5783a2fd4a773b11618d8a877adb5080af41b4233035e3f4f6168c36e8','provider audit pin')
base=json.loads(STATE.read_text());need(base['status']=='PASS' and len(base['rows'])==1 and base['rows'][-1]['module']=='Sign17KRankedRawWord','provider status')
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
need(sha(P/'source-manifest.json')=='6a781ae8d11840d03678b86bcaa04d9f0d1ad5f93a82e1b0f0e71d663b0cec2e','manifest pin')
entries=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(entries)==3,'stage count');names=[e['module'].split('.')[-1] for e in entries];need(len(names)==len(set(names)),'duplicate names')
witness=D/'research/nine-sharing-sign17-k-ranking-witness/witness.json'
need(sha(witness)=='7f50654d30197158157533857892ddde91b7234bfdfe0cc6089282e5613b81a3','witness pin')
need(sha(D/'reviews/nine-sharing-sign17-k-ranking-witness-independent/check.py')=='9572d4eec346374dcc989fb070f4a488f06317a486efd36443818782e5f70150','witness audit')
rows=json.loads(witness.read_text())['rows'];need(len(rows)==942 and [r['physical'] for r in rows]==list(range(942)),'witness rows')
need(rows[0]['index']==0 and all(r['index']!=0 for r in rows[1:]) and all(rows[i]['weight']>rows[i+1]['weight'] for i in range(1,941)),'external candidate facts')
coeffs=D/'research/padding-staircase-independent/coefficients.json';need(sha(coeffs)=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93','external coefficient pin')
need(sha(D/'research/nine-sharing-sign17-k-control-coefficients-draft/generate.py')=='c66358a11a2cd7fbbb7248dbfe4d3462fba78059a04de37dd6e9b04a942b9f9f','generator pin')
src=(P/'src/DiophantineConsistency/Sign17KControlBlocks.lean').read_text();found=re.findall(r'^def literal : Fin 44 → ℕ := !\[([^]]*)\]$',src,re.M);need(len(found)==1,'control vector syntax')
external=json.loads(coeffs.read_text());expected=[0]*44
for start,n,bit in [(942,9,35),(960,9,18),(969,8,27),(978,8,10)]:
 for j in range(n):expected[start+j-942]+=2*2**(bit+j)
need([int(x.strip()) for x in found[0].split(',')]==expected==external[942:986],'external control slice')
failed_state=D/'research/nine-sharing-sign17-k-control-coefficients-check/attempt01/state.json';failed_outer=failed_state.parent/'outer-result.json'
need(sha(failed_state)=='1f4d1730623fb6412a4a077b435044d8de887756b707c3e12d46215139517414','timeout state')
need(sha(failed_outer)=='ee274dd8daafe3cb81fb0f9e12b971129775529874f4ded1ccd6091af263cd14' and json.loads(failed_outer.read_text())['outer_exit_code']==1,'timeout outer')
need(sha(D/'reviews/nine-sharing-sign17-k-control-coefficients-terminal-independent/check.py')=='c8989b51429e0ac12f9b4d855210a92a912411ed5e2286bbfff016250e014460','timeout audit')
failed=json.loads(failed_state.read_text());need(failed['status']=='FAILED' and failed['rows'][0]['compile']['stop_reason']=='timeout','timeout status')
for folder,sp,op,ap,idx in [('append','dcb0ff959917bdf0e0d7f4a3deaca2fbde1a24fee17c3ca65c69d2ef2f3ec142','968eea7026b3993d441a64e9af4c1fda1b47987c914a7eae76ebaa0314230331','7c04ac869f106431667d1871aa6c02e9597c81394990febd4eb43146b6fa436b',1),('blocks','df16a92a1ddf2a7b13b05d06061eb39972b621f1eed37850de1ebd57291c9c4f','7e139cfcdd1ea1ad8aec9346c60e7c285125ccc12ddac233879e87bb3b4c8e80','295d5c9319dbc10383d99bc614c0fae34efee202ee288712116b52195bafb19a',0)]:
 st=D/'research'/('nine-sharing-sign17-k-control-'+folder+'-check')/'attempt01/state.json';ou=st.parent/'outer-result.json';au=D/'reviews'/('nine-sharing-sign17-k-control-'+folder+'-terminal-independent')/'check.py'
 need(sha(st)==sp and sha(ou)==op and sha(au)==ap and json.loads(ou.read_text())['outer_exit_code']==0,'ingredient receipt '+folder)
 rec=json.loads(st.read_text());need(rec['status']=='PASS' and len(rec['rows'])==1 and rec['rows'][0]['source_sha256']==entries[idx]['source_sha256'],'ingredient source '+folder)
provider_names={r['module']:r for r in base['rows']};seen=set()
for e in entries:
 n=e['module'].split('.')[-1];src=P/'src/DiophantineConsistency'/(n+'.lean');need(sha(src)==e['source_sha256'] and sha(REPO/e['source'])==e['source_sha256'],'source pin '+n)
 need(not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean')),'provider collision '+n)
 need(re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==e['imports'],'imports '+n)
 for m in e['imports']:
  local=m.split('.')[-1];need(local in provider_names or local in seen,'unexpected or unordered import '+m)
 seen.add(n)
if sys.argv[1:]==['--preflight']:
 print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','stage_count':len(entries),'scope':'Audited single-context provider and direct source/object/guard observations; no Lean, complete transitive trace, global order or rank proof.'},sort_keys=True));raise SystemExit(0)
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
   if depname in provider_names:path=BASE/'lib/DiophantineConsistency'/(depname+'.olean');expected=provider_names[depname]['object_sha256']
   else:
    prior=[r for r in state['rows'][:-1] if r['module']==depname];need(len(prior)==1,'local producer '+mod);path=OUT/'lib/DiophantineConsistency'/(depname+'.olean');expected=prior[0]['object_sha256']
   need(rec['sha256']==expected and rec['realpath']==str(path.resolve()),'direct producer '+mod)
  row['dependencies']=deps;row['direct_guard']=guard(deps);save();log=OUT/(n+'-compile.txt');obj=OUT/'lib/DiophantineConsistency'/(n+'.olean')
  res=monitor.run(prefix+['--root='+str(OUT/'src'),str(src),'-o',str(obj)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['compile']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'compile failed '+n)
  need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",log.read_text()) and obj.is_file(),'errors '+n);need(guard(deps)==row['direct_guard'],'guard drift '+n);row['object_sha256']=sha(obj);save()
 for entry,row in zip(entries,state['rows']):
  need(sha(OUT/'lib/DiophantineConsistency'/(row['module']+'.olean'))==row['object_sha256'] and guard(row['dependencies'])==row['direct_guard'],'final drift '+row['module'])
 for k,v in links.items():need(Path(k).is_symlink() and str(Path(k).resolve())==v,'final overlay '+k)
 state['status']='PASS';save();print('PASS K control block sum')
except BaseException as e:
 state['status']='FAILED';state['exception']=repr(e);save();raise
