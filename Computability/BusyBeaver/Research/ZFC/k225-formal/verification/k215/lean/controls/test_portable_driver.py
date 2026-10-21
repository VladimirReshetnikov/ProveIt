#!/usr/bin/env python3
"""Own noncompiler controls for the portable serial supervisor and exact source inventory."""
from pathlib import Path
import importlib.util,json,signal,subprocess,sys,os,time
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
SCRIPT=ROOT/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py'
P=Path('/tmp/k215-lean-complete/portable-controls');P.mkdir(exist_ok=False)
spec=importlib.util.spec_from_file_location('driver',SCRIPT);d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)
inv=d.inventory(ROOT);actual=json.loads(Path('/tmp/k215-lean-complete/inventory-v2.json').read_text())
assert len(inv['modules'])==204
assert inv['external_imports']==['Init']
assert [x['module'] for x in inv['modules']]==actual['order']
for x,y in zip(inv['modules'],actual['project_modules']):
 assert x['module']==y['module'] and x['imports']==y['imports']
 assert x['source']==str(ROOT/y['relative_source']) and x['source_sha256']==y['sha256']
lock=P/'test.lock'
def command(case):
 return [sys.executable,'-c',"import os,subprocess,sys,time; from pathlib import Path; p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)']); Path(sys.argv[1]).write_text(str(os.getpid())+' '+str(p.pid)); time.sleep(60)",str(P/(case+'.pids'))]
def dead(pid):
 p=Path('/proc')/str(pid)/'stat'
 return not p.exists() or p.read_text().split()[2]=='Z'
records=[]
for case in ('timeout','interruption'):
 row={'command':command(case)}
 if case=='interruption':
  def alarm(s,f):raise KeyboardInterrupt('control only')
  signal.signal(signal.SIGALRM,alarm);signal.setitimer(signal.ITIMER_REAL,.8)
 try:
  ok=d.run_locked(row['command'],P,os.environ.copy(),lock,P/(case+'.log'),.4 if case=='timeout' else 10,row,P/(case+'.json'))
  assert case=='timeout' and not ok
 except KeyboardInterrupt:
  assert case=='interruption'
 finally:signal.setitimer(signal.ITIMER_REAL,0)
 pids=list(map(int,(P/(case+'.pids')).read_text().split()))
 for _ in range(100):
  if all(dead(pid) for pid in pids):break
  time.sleep(.01)
 assert all(dead(pid) for pid in pids),(case,pids)
 # An independent process can acquire only after cleanup returned.
 check=subprocess.run([sys.executable,'-c','import fcntl,sys; f=open(sys.argv[1],"a+"); fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)',str(lock)])
 assert check.returncode==0
 records.append({'case':case,'pids':pids,'no_live_children':True,'lock_released_after_cleanup':True,'record_sha256':d.sha(P/(case+'.json'))})
row={};ok=d.run_locked([sys.executable,'-c','print("success control")'],P,os.environ.copy(),lock,P/'success.log',5,row,P/'success.json');assert ok
result={'status':'PASS','scope':'Own noncompiler controls only; no Lean, Lake, Rocq or supplied proof replay.','driver_sha256':d.sha(SCRIPT),'test_sha256':d.sha(Path(__file__)),'inventory_modules':204,'exact_source_import_order_and_hashes_match_actual_inventory':True,'controls':records,'normal_success':True}
d.save(P/'result.json',result);print(json.dumps(result,indent=2))
