#!/usr/bin/env python3
"""Check mapped GG corollaries over independently audited captured P13/P14."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];OUT=Path('/tmp/p72-p13-p14-translated-captured-20261105');PREV=Path('/tmp/p72-p13-p14-captured-endpoint-20261105');PKT=D/'research/p72-p13-p14-captured-endpoint-replay';REVIEW=D/'reviews/p72-p13-p14-captured-endpoint-independent/check.py';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';roots=[OUT/'lib',TOOL];SUF=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
def save():
 p=OUT/'state.tmp';p.write_text(json.dumps(state,sort_keys=True,indent=2)+'\n');os.replace(p,OUT/'state.json')
def available():
 for line in Path('/proc/meminfo').read_text().splitlines():
  if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
 raise RuntimeError('missing MemAvailable')
def no_lean():
 for p in Path('/proc').iterdir():
  if not p.name.isdecimal():continue
  try:
   if (p/'comm').read_text().strip()=='lean' and (p/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X'):return False
  except (FileNotFoundError,ProcessLookupError):continue
 return True
pins={P/'P72Translated.lean':'324803ca69036a8731c1bb9a65fd635e8a48d29a998c57023eef8f6f1901691a',MON:'d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad',REVIEW:'86ce4cac5a576d3eb07d0fdf83a675cdb9e572161b1626c4d0d89d5330528884',PKT/'attempt01/state.json':'69b125385c7eff4a1ae2efcde94f777e16c591fb281b07e0132500173f9df2aa',PKT/'attempt01/outer-terminal.json':'3e5b49c82d35560fa9534491c5c06ce1cf95441aaae7ae7785ed33e5ae4b7cb2',PREV/'lib/DiophantineConsistency/Compact44/IPRAOrdinary72.olean':'d667e5803d918e9211c170e55a03d56d8b62b42f43b152d8ab526905ae26a3b3',PREV/'lib/DiophantineConsistency/Compact44/IPRAOrdinary72P14.olean':'3c47dcbbd39cbb2f89092e40d747366589cc618da7bdf9765016554d65e82468'}
def preflight():
 for p,h in pins.items():need(p.is_file() and sha(p)==h,'input drift '+str(p))
 q=subprocess.run([sys.executable,'-I','-S','-B',str(REVIEW)],capture_output=True,timeout=120);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)['status']=='PASS','endpoint review failure')
 need(available()>=10*1024**3 and shutil.disk_usage('/tmp').free>=5_000_000_000,'resource preflight')
def guard(names):
 out={}
 for n in sorted(names):
  for r in roots:
   for suffix in SUF:
    p=r/(n.replace('.','/')+suffix)
    if os.path.lexists(p):need(p.is_file(),'bad candidate '+str(p));out[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
    else:out[str(p)]=None
 return out
need(not OUT.exists() and no_lean(),'output exists or Lean active');runner=sha(__file__);preflight();prev=json.loads((PKT/'attempt01/state.json').read_text());need(prev['status']=='PASS','prior status');OUT.mkdir();state={'status':'RUNNING','runner_sha256':runner,'pins':{str(k):v for k,v in pins.items()},'scope':'P13/P14 translated corollaries over captured P64/P65 ancestry; no fresh base rebuild, complete dynamic import trace, Lean JSON or byte-file theorem. Sampled limits may miss spikes or escaped processes.'};save()
spec=importlib.util.spec_from_file_location('mon',MON);mon=importlib.util.module_from_spec(spec);spec.loader.exec_module(mon)
try:
 links={}
 for rel,(kind,target) in prev['overlay_links'].items():
  p=OUT/'lib'/rel;p.parent.mkdir(parents=True,exist_ok=True);need(not os.path.lexists(p),'overlay conflict '+rel);p.symlink_to(target,target_is_directory=kind=='dir');links[str(p)]=target
 for n in ('IPRAOrdinary72','IPRAOrdinary72P14'):
  src=PREV/'lib/DiophantineConsistency/Compact44'/(n+'.olean');p=OUT/'lib/DiophantineConsistency/Compact44'/(n+'.olean');p.parent.mkdir(parents=True,exist_ok=True);need(not os.path.lexists(p),'endpoint shadow '+n);p.symlink_to(src.resolve());links[str(p)]=str(src.resolve())
 state['overlay_links']=links;save();source=OUT/'src/DiophantineConsistency/P72Translated.lean';source.parent.mkdir(parents=True);shutil.copyfile(P/'P72Translated.lean',source);need(sha(source)==pins[P/'P72Translated.lean'],'source copy')
 env=dict(os.environ,LEAN_PATH=str(OUT/'lib'),LEAN_NUM_THREADS='1')
 for k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(k,None)
 prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M4000','-j1','-DElab.async=false'];obj=OUT/'lib/DiophantineConsistency/P72Translated.olean';state['runs']=[]
 for typ,args in [('deps',['--deps',str(source)]),('compile',['--root='+str(OUT/'src'),str(source),'-o',str(obj)])]:
  need(available()>=10*1024**3 and shutil.disk_usage('/tmp').free>=5_000_000_000,'stage resources');log=OUT/(typ+'.txt');m=mon.run(prefix+args,OUT,env,log,rss_limit=5*1024**3,mem_floor=10*1024**3,seconds=180,interval=.1);state['runs'].append({'command':prefix+args,**m,'log_sha256':sha(log)});save();need(m['exit']==0 and m['stop_reason'] is None and not m['monitor_errors'] and not m['observed_descendant_pids'],'Lean '+typ+' failure')
  if typ=='deps':
   actual={};counts={}
   for line in log.read_text().splitlines():
    p=Path(line);hits=[r for r in roots if p.is_relative_to(r)];need(p.is_absolute() and p.is_file() and line.endswith('.olean') and len(hits)==1,'bad dependency '+line);n=str(p.relative_to(hits[0]))[:-6].replace('/','.');counts[n]=counts.get(n,0)+1;need(n not in actual or (n=='Init' and counts[n]<=2 and actual[n]['path']==line),'duplicate dependency');actual[n]={'path':line,'realpath':str(p.resolve()),'sha256':sha(p)}
   need(set(actual)-{'Init'}=={'DiophantineConsistency.Compact44.IPRAOrdinary72P14'},'unexpected imports');need(actual['DiophantineConsistency.Compact44.IPRAOrdinary72P14']['sha256']==pins[PREV/'lib/DiophantineConsistency/Compact44/IPRAOrdinary72P14.olean'],'wrong P14 provider');state['dependencies']=actual;state['direct_guard']=guard(actual);save()
 text=(OUT/'compile.txt').read_text();need('error:' not in text and 'sorryAx' not in text and obj.is_file(),'compile error')
 for n in ('standard_translated_p13','standard_translated_p14'):
  reports=re.findall(r"'DiophantineConsistency.P72Translated."+n+r"' depends on axioms: \[([^]]*)\]",text);need(len(reports)==1 and set(x.strip() for x in reports[0].split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},'axiom report '+n)
 need(guard(state['dependencies'])==state['direct_guard'],'guard drift')
 for p,target in links.items():need(Path(p).is_symlink() and str(Path(p).resolve())==target,'overlay drift '+p)
 preflight();need(sha(__file__)==runner,'runner drift');state['object_sha256']=sha(obj);state['status']='PASS';save();print('PASS captured P13/P14 GG translated corollaries',flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
