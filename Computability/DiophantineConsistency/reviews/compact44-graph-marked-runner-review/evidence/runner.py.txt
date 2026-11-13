#!/usr/bin/env python3
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys,time,traceback
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge'
PLAN=BASE/'compact44-graph-marked-join-plan'; GRAPH=Path('/tmp/compact44-graph-support-join-01/lib'); PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'); OUT=Path('/tmp/ipra-graph-marked-explore-03'); LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'); MON=BASE/'free-j-current-denominator-composition/replay.py'
SUF=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def need(p,msg):
 if not p:raise ValueError(msg)
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def record(p):
 if not os.path.lexists(p):return None
 need(p.is_file(),('not a regular live input',str(p)))
 return {'realpath':str(p.resolve(strict=True)),'sha256':H(p)}
def slotstem(p):return {str(Path(str(p)+s)):record(Path(str(p)+s)) for s in SUF}
def check(all):
 for p,v in all.items():need(record(Path(p))==v,('input drift',p))
def diagnostics_ok(name, text, source_sha):
 if re.search(r'(?m)^.*error:|\bsorryAx\b|\bsorry\b',text):return False
 if 'warning:' not in text:return True
 survey=Path('/tmp/graph-marked-warning-survey-01.json');need(H(survey)=='6546baaf4f534dcd3f4d59605fda50edd2a73de7b5d8c58de7a81996ca47678c','warning survey drift')
 record=json.loads(survey.read_text())['matched'].get(name)
 if record is None or record['warning_count']<=0 or record['source_sha256']!=source_sha:return False
 historical=ROOT/record['historical_log'];need(historical.is_file() and H(historical)==record['historical_log_sha256'],'historical warning log drift')
 normalize=lambda s: re.sub(r'(?m)^.*?(?=:\d+:\d+: warning:)', '<SOURCE>', s)
 return text.count('warning:')==record['warning_count'] and normalize(text)==normalize(historical.read_text())
def main():
 need(not os.path.lexists(OUT),'output path exists'); need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk below 4GiB')
 a=json.loads((PLAN/'busybeaver-source-scan.json').read_bytes());b=json.loads((PLAN/'source-scan.json').read_bytes());need(not a['unresolved'] and not b['unresolved'],'unresolved candidate scan')
 rows=[]
 for i,row in enumerate(a['ordered_sources']+b['ordered_sources']):
  name=row['module']; name=name if '.' in name else 'DiophantineConsistency.'+name
  p=ROOT/row['source'];need(p.is_file() and H(p)==row['sha256'],('source mismatch',str(p)))
  imp=re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M);need(imp==row['imports'],('import drift',name));rows.append({'module':name,'source':str(p),'source_sha256':H(p),'imports':imp})
 names=[x['module'] for x in rows];need(len(rows)==100 and len(set(names))==100,'source count or duplicate mismatch')
 spec=importlib.util.spec_from_file_location('resource_monitor',MON);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 OUT.mkdir(); frozen=OUT/'frozen';lib=OUT/'lib';frozen.mkdir();m.overlay(GRAPH,lib)
 env=os.environ.copy()
 for k in tuple(env):
  if k.startswith('PYTHON') or k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(k,None)
 env['LEAN_PATH']=str(lib)+':'+str(PKG)
 sourceguards={}; directguards={}; produced=set();input_inv={};target_inv={}
 for x in rows:
  name=x['module'];p=Path(x['source']);dst=(frozen/Path(*name.split('.'))).with_suffix('.lean');dst.parent.mkdir(parents=True,exist_ok=True);need(not os.path.lexists(dst),'frozen source collision');shutil.copyfile(p,dst);need(H(dst)==x['source_sha256'],'frozen copy mismatch');x['frozen']=str(dst);sourceguards[str(dst)]=H(dst)
  target=(lib/Path(*name.split('.'))).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True);need(not os.path.lexists(target),('target collision',name,str(target)));target_inv[name]=slotstem(Path(str(target)[:-6]));need(all(v is None for v in target_inv[name].values()),('target companion collision',name))
  dependencies={}
  for dep in ['Init']+x['imports']:
   if dep in produced:dependencies[dep]={'role':'earlier_same_overlay'};continue
   need(dep not in names,('import before build',name,dep));rel=Path(*dep.split('.')).with_suffix('.olean');providers=[lib/rel,PKG/rel];present=[p for p in providers if p.is_file()];need(present,('missing direct input',name,dep,[str(p) for p in providers]));chosen=present[0];need(all(H(p)==H(chosen) for p in present),('different collisions',name,dep,[str(p) for p in present]));dependencies[dep]={'role':'direct_seed' if chosen.is_relative_to(lib) else 'package','path':str(chosen),'realpath':str(chosen.resolve()),'sha256':H(chosen),'also_present':[str(p) for p in present[1:]]};directguards.update(slotstem(Path(str(chosen)[:-6])))
  input_inv[name]=dependencies;produced.add(name)
 need(LEAN.is_file(),'missing Lean');check(directguards)
 inv={'status':'READY_AUTHOR_ONLY_NO_LEAN','source_count':len(rows),'sources':rows,'direct_inputs':input_inv,'direct_companion_slots':directguards,'target_companion_slots':target_inv,'seed_overlay':str(GRAPH),'package':str(PKG),'lean':str(LEAN),'lean_sha256':H(LEAN),'monitor_sha256':H(MON),'disk_free_bytes':shutil.disk_usage('/tmp').free,'ancestry_limitation':'Exploratory author graph seed, packages and their transitive/dynamic dependencies are not authenticated by this inventory.'}
 (OUT/'preflight.json').write_text(json.dumps(inv,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':inv['status'],'source_count':len(rows),'direct_slots':len(directguards),'target_slots':sum(len(x) for x in target_inv.values()),'disk_free_bytes':inv['disk_free_bytes']}),flush=True)
 if '--preflight-only' in sys.argv:return
 outputs={};steps=[]
 for i,x in enumerate(rows):
  check(directguards)
  for p,h in sourceguards.items():need(Path(p).is_file() and not Path(p).is_symlink() and H(Path(p))==h,('frozen source drift',p))
  name=x['module'];src=Path(x['frozen']);obj=(lib/Path(*name.split('.'))).with_suffix('.olean');need(all(v is None for v in slotstem(Path(str(obj)[:-6])).values()),('output collision at child',name))
  expected=set()
  for dep in ['Init']+x['imports']:
   rel=Path(*dep.split('.')).with_suffix('.olean');chosen=next((p for p in [lib/rel,PKG/rel] if p.is_file()),None);need(chosen is not None,('missing compile input',name,dep));expected.add(str(chosen.resolve()))
  dp=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120)
  got={str(Path(x).resolve()) for x in dp.stdout.splitlines() if x.strip()};need(dp.returncode==0 and not dp.stderr and got==expected,('deps mismatch',name,dp.returncode,dp.stdout,dp.stderr,sorted(expected)))
  check(directguards);cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={frozen}',str(src),'-o',str(obj)];log=OUT/(str(i+1).zfill(3)+'-'+name.replace('.','_')+'.log');code,peak,reason=m.monitored(cmd,env,log,timeout=600);output=log.read_text(); step={'position':i+1,'module':name,'compiler_exit':code,'reason':reason,'peak_sampled_rss_bytes':peak,'log':str(log),'log_sha256':H(log),'deps_exit':dp.returncode,'deps_stdout':dp.stdout,'command':cmd,'disk_free_bytes':shutil.disk_usage('/tmp').free};steps.append(step);(OUT/'progress.json').write_text(json.dumps({'steps':steps},indent=2)+'\n');print(json.dumps(step),flush=True)
  need(type(code) is int and code==0 and reason is None,('child failed',name,code,reason));need(diagnostics_ok(name,output,x['source_sha256']),('diagnostic rejected',name,output[-8000:]));need(obj.is_file() and not obj.is_symlink(),('missing output',name));outguard=slotstem(Path(str(obj)[:-6]));need(all((v is not None) if p==str(obj) else v is None for p,v in outguard.items()),('unexpected output companion',name));directguards.update(outguard);outputs[name]=H(obj);check(directguards)
 (OUT/'RESULT.json').write_text(json.dumps({'status':'PASS_AUTHOR_ONLY_EXPLORATORY_REBUILD','steps':steps,'objects':outputs,'limitations':inv['ancestry_limitation']},indent=2)+'\n');print('PASS_AUTHOR_ONLY_EXPLORATORY_REBUILD',flush=True)
try:main()
except Exception as e:
 print('EXPLORATION_FAILED',repr(e),flush=True);traceback.print_exc();sys.exit(1)
