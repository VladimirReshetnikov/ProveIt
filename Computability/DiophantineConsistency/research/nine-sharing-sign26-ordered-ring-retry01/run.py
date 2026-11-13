#!/usr/bin/env python3
"""Bounded, isolated check of three ordered-ring lemmas; no model bridge."""
import hashlib,importlib.util,json,os,re,shutil,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];OUT=Path('/tmp/sign26-ordered-ring-retry01-20261106');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean';MON=D/'research/thirteen-current2011-complete-4g-retry/monitor.py';DRAFT=D/'research/nine-sharing-sign26-ordered-ring-retry01-draft/Sign26OrderedRing.lean';SRC=P/'src/Sign26OrderedRing.lean';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,msg):
 if not v:raise RuntimeError(msg)
need(sha(P/'input-pins.json')=='b875158725f89fd2700028a0f5e27c5ccf2884437117cef96426bb5c12ab3b1c','pins');pins=json.loads((P/'input-pins.json').read_text());need(not OUT.exists(),'output exists');need(sha(SRC)==pins['source_sha256'] and sha(DRAFT)==pins['draft_sha256'] and sha(LEAN)==pins['lean_sha256'] and sha(MON)==pins['monitor_sha256'],'source/tool pins')
need(SRC.read_bytes()==DRAFT.read_bytes(),'draft source drift');need(re.findall(r'^import ([A-Za-z0-9_.]+)$',SRC.read_text(),re.M)==pins['modules'][1:],'source imports')
def guard():
 result={}
 for path,want in pins['direct_candidate_guard'].items():
  p=Path(path)
  if os.path.lexists(p):need(p.is_file(),'bad candidate '+path);actual={'realpath':str(p.resolve()),'sha256':sha(p)}
  else:actual=None
  need(actual==want,'candidate drift '+path);result[path]=actual
 return result
before=guard()
for root in (PKG,TOOL):need(not os.path.lexists(root/'Sign26OrderedRing.olean'),'target collision')
if sys.argv[1:]==['--preflight']:
 print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','guard_slots':len(before),'scope':'Pinned source, tool and direct-candidate point checks only; no Lean or full package-transitive trace.'},sort_keys=True));raise SystemExit(0)
need(not sys.argv[1:],'unexpected arguments')
for proc in Path('/proc').iterdir():
 if not proc.name.isdecimal():continue
 try:need(not ((proc/'comm').read_text().strip()=='lean' and (proc/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X')),'another Lean process is active')
 except (FileNotFoundError,ProcessLookupError):continue
need(shutil.disk_usage('/tmp').free>=5_000_000_000 and int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024>=10*1024**3,'resources')
spec=importlib.util.spec_from_file_location('monitor',MON);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
OUT.mkdir();(OUT/'src').mkdir();(OUT/'lib').mkdir();shutil.copyfile(SRC,OUT/'src/Sign26OrderedRing.lean');state={'status':'RUNNING','scope':'Generic gap congruence and conditional sign only; source/model bridge absent. Point provider guards and sampled monitor.','runner_sha256':sha(__file__),'source_sha256':pins['source_sha256'],'input_pins_sha256':sha(P/'input-pins.json'),'direct_guard':before,'rows':[]}
def save():
 p=OUT/'state.tmp';p.write_text(json.dumps(state,sort_keys=True,indent=2)+'\n');os.replace(p,OUT/'state.json')
save()
try:
 env=dict(os.environ,LEAN_PATH=str(PKG),LEAN_NUM_THREADS='1')
 for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
 prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M2800','-j1','-DElab.async=false'];src=OUT/'src/Sign26OrderedRing.lean';row={'module':'Sign26OrderedRing','source_sha256':sha(src)};state['rows'].append(row);save()
 log=OUT/'Sign26OrderedRing-deps.txt';res=monitor.run(prefix+['--deps',str(src)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['deps']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'deps failed')
 deps={};counts={}
 for line in log.read_text().splitlines():
  p=Path(line);hits=[r for r in (PKG,TOOL) if p.is_relative_to(r)];need(p.is_absolute() and p.is_file() and line.endswith('.olean') and len(hits)==1,'bad dependency '+line);mod=str(p.relative_to(hits[0]))[:-6].replace('/','.');counts[mod]=counts.get(mod,0)+1;need(mod not in deps or (mod=='Init' and counts[mod]<=2 and deps[mod]['path']==line),'duplicate dependency '+mod);deps[mod]={'path':line,'realpath':str(p.resolve()),'sha256':sha(p)}
 need(set(deps)==set(pins['modules']),'unexpected dependency set')
 for mod,rec in deps.items():
  candidates=[root/(mod.replace('.','/')+'.olean') for root in (PKG,TOOL) if (root/(mod.replace('.','/')+'.olean')).is_file()];need(candidates and str(candidates[0])==rec['path'] and pins['direct_candidate_guard'][rec['path']]=={'realpath':rec['realpath'],'sha256':rec['sha256']},'dependency route '+mod)
 row['dependencies']=deps;save();log=OUT/'Sign26OrderedRing-compile.txt';obj=OUT/'lib/Sign26OrderedRing.olean';res=monitor.run(prefix+['--root='+str(OUT/'src'),str(src),'-o',str(obj)],OUT,env,log,rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1);row['compile']={**res,'log_sha256':sha(log)};save();need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and not res['observed_descendant_pids'],'compile failed');need(obj.is_file() and not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",log.read_text()),'compile errors');need(sha(src)==sha(SRC)==pins['source_sha256'] and sha(DRAFT)==pins['draft_sha256'] and sha(LEAN)==pins['lean_sha256'] and sha(MON)==pins['monitor_sha256'] and sha(P/'input-pins.json')=='b875158725f89fd2700028a0f5e27c5ccf2884437117cef96426bb5c12ab3b1c' and guard()==before,'final source/tool/guard drift');row['object_sha256']=sha(obj);state['status']='PASS';save();print('PASS sign26 generic ordered-ring import retry')
except BaseException as e:
 state['status']='FAILED';state['failure']=repr(e);save();print('FAILED',repr(e));raise
