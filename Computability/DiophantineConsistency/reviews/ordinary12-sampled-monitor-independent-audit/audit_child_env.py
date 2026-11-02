#!/usr/bin/env python3
"""Exercise child optimization sanitization after monitor import."""
import hashlib,importlib.util,json,os,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];TASK=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/difference-ring-build-plan/monitor';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ('monitor.py','paired.py','path_guard.py'):
 p=TASK/name;assert subprocess.check_output(['git','show','0f09b04dec:'+str(p.relative_to(ROOT))],cwd=ROOT)==p.read_bytes()
env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None)
for name in ('monitor.py','paired.py'):
 p=subprocess.run([sys.executable,'-O',str(TASK/name),'--help'],env=env,capture_output=True,text=True,timeout=10);assert p.returncode!=0 and 'optimized Python' in p.stderr
os.environ.pop('PYTHONOPTIMIZE',None);sys.path.insert(0,str(TASK));spec=importlib.util.spec_from_file_location('monitor_independent_env',TASK/'monitor.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
with tempfile.TemporaryDirectory(prefix='ipra-monitor-child-env-') as td:
 os.environ['PYTHONOPTIMIZE']='1'
 try:
  result=mod.run(Path(td)/'run',[sys.executable,'-c','import os,sys; assert sys.flags.optimize==0 and "PYTHONOPTIMIZE" not in os.environ; print("PASS_CHILD_OPTIMIZATION_DISABLED")'],reserve=0,budget=1000000,interval=.02,grace=.1)
 finally:os.environ.pop('PYTHONOPTIMIZE',None)
 assert result['status']=='EXITED' and result['outer_exit_code']==0 and (Path(td)/'run/child.log').read_text().strip()=='PASS_CHILD_OPTIMIZATION_DISABLED'
r={'status':'PASS_INDEPENDENT_MONITOR_CHILD_ENV_AUDIT','commit':'0f09b04dec','monitor_sha256':H(TASK/'monitor.py'),'paired_sha256':H(TASK/'paired.py'),'direct_dash_O_both_rejected':True,'post_import_env_mutation_child_optimization_disabled':True,'scope':'Toy child, no Lean build; does not alter direct use of the historical builder.'};out=HERE/'child-env-receipt.json'
if out.exists():raise ValueError('refusing overwrite')
out.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['status'],H(out))
