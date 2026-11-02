#!/usr/bin/env python3
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys,traceback
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs'); PARENT=Path('/tmp/ipra-graph-marked-explore-03'); OUT=Path('/tmp/ipra-wangtable-highmem-explore-02'); PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'); LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'); MON=Path('/tmp/wangtable-monitor-staging/v1/monitor.py')
SUF=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def state(p):
 if not os.path.lexists(p):return None
 need(p.is_file(),('invalid input',str(p)));return {'realpath':str(p.resolve()),'sha256':H(p)}
def slots(p):return {str(Path(str(p)+s)):state(Path(str(p)+s)) for s in SUF}
def check(g):
 for p,v in g.items():need(state(Path(p))==v,('slot drift',p))
def main():
 need(not os.path.lexists(OUT),'output exists');need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk reserve');pre=json.loads((PARENT/'preflight.json').read_text()); steps=json.loads((PARENT/'progress.json').read_text())['steps'];need(len(steps)==82 and all(x['compiler_exit']==0 for x in steps[:81]) and steps[-1]['module']=='DiophantineConsistency.ArithmeticWangTable' and steps[-1]['compiler_exit']==1,'unexpected parent prefix')
 row=next(x for x in pre['sources'] if x['module']=='DiophantineConsistency.ArithmeticWangTable');src=Path(row['frozen']);need(src.is_file() and H(src)==row['source_sha256'],'source mismatch');spec=importlib.util.spec_from_file_location('monitor',MON);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor);OUT.mkdir();lib=OUT/'lib';monitor.overlay(PARENT/'lib',lib);frozen=OUT/'frozen';dst=frozen/'DiophantineConsistency'/'ArithmeticWangTable.lean';dst.parent.mkdir(parents=True);shutil.copyfile(src,dst);need(H(dst)==row['source_sha256'],'frozen source mismatch');obj=lib/'DiophantineConsistency/ArithmeticWangTable.olean';before=slots(Path(str(obj)[:-6]));need(all(v is None for v in before.values()),'output collision')
 guards={};expected=set(); resolution={}
 for dep in ['Init']+row['imports']:
  rel=Path(*dep.split('.')).with_suffix('.olean'); choices=[lib/rel,PKG/rel]; states=[state(p) for p in choices];chosen=next((p for p in choices if p.is_file()),None);need(chosen is not None,('missing dependency',dep));need(all(s is None or s['sha256']==H(chosen) for s in states),('different providers',dep));resolution[dep]={'choices':[str(x) for x in choices],'states':states,'chosen':str(chosen)};expected.add(str(chosen.resolve()));
  for p in choices:guards.update(slots(Path(str(p)[:-6])))
 check(guards);env=os.environ.copy()
 for k in tuple(env):
  if k.startswith('PYTHON') or k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(k,None)
 env['LEAN_PATH']=str(lib)+':'+str(PKG);deps=subprocess.run([str(LEAN),'--deps',str(dst)],env=env,capture_output=True,text=True,timeout=120);need(deps.returncode==0 and not deps.stderr and {str(Path(x).resolve()) for x in deps.stdout.splitlines() if x.strip()}==expected,('deps mismatch',deps.returncode,deps.stdout,deps.stderr));check(guards)
 command=[str(LEAN),'-M6000','-j1','-DElab.async=false',f'--root={frozen}',str(dst),'-o',str(obj)];initial={'source_sha256':H(dst),'parent_preflight_sha256':H(PARENT/'preflight.json'),'parent_progress_sha256':H(PARENT/'progress.json'),'monitor_sha256':H(MON),'resolution':resolution,'input_guards':guards,'output_before':before,'deps_stdout':deps.stdout,'deps_exit':deps.returncode,'command':command,'free_disk_before':shutil.disk_usage('/tmp').free,'limitations':'author prefix and its transitive package ancestry are not independently authenticated'};(OUT/'preflight.json').write_text(json.dumps(initial,indent=2,sort_keys=True)+'\n');print('READY_SINGLE_CHILD',flush=True)
 code,peak,reason=monitor.monitored(command,env,OUT/'compiler.log',timeout=600);output=(OUT/'compiler.log').read_text(); result={'compiler_exit':code,'reason':reason,'peak_sampled_rss_bytes':peak,'log_sha256':H(OUT/'compiler.log'),'free_disk_after':shutil.disk_usage('/tmp').free};(OUT/'child-result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result),flush=True);need(type(code) is int and code==0 and reason is None,'compiler failed');need(not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',output),'diagnostic rejected');need(obj.is_file() and not obj.is_symlink(),'missing output');after=slots(Path(str(obj)[:-6]));need(all((v is not None) if k==str(obj) else v is None for k,v in after.items()),'unexpected output companion');check(guards);need(H(dst)==row['source_sha256'],'source drift');result['object_sha256']=H(obj);result['status']='PASS_SINGLE_AUTHOR_WANGTABLE_EXPLORATION';(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],flush=True)
try:main()
except Exception as e:
 print('EXPLORATION_FAILED',repr(e),flush=True);traceback.print_exc();sys.exit(1)
