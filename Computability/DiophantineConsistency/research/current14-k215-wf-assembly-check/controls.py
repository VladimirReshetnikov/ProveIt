#!/usr/bin/env python3
"""Non-Lean controls for resource/report, output refusal and monitor termination."""
import importlib.util,json,os,sys,tempfile
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('coherent_runner_control',P/'run.py');runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
runner.self_test()
original=runner.OUT;runner.OUT=P
try:
 try:runner.preflight()
 except runner.Refusal as e:
  if 'output already exists' not in str(e):raise
 else:raise RuntimeError('preexisting output accepted')
finally:runner.OUT=original
# A run must start its watchdog before entering initial preflight.
original_watch,original_preflight=runner.Watch,runner.preflight;watch_observation={}
class ProbeWatch:
 def __init__(self,start):self.started=False;self.stopped=False;watch_observation['instance']=self
 def begin(self):self.started=True
 def check(self):pass
 def stop(self):self.stopped=True
def refuse_preflight():
 active=runner.ACTIVE_WATCH
 if not isinstance(active,ProbeWatch) or not active.started:raise RuntimeError('preflight started without watchdog')
 raise runner.Refusal('synthetic preflight refusal')
runner.Watch,runner.preflight=ProbeWatch,refuse_preflight
try:
 try:runner.run()
 except runner.Refusal as e:
  if 'synthetic preflight refusal' not in str(e):raise
 else:raise RuntimeError('preflight refusal was ignored')
 if not watch_observation['instance'].stopped or runner.ACTIVE_WATCH is not None:raise RuntimeError('preflight watchdog was not cleaned up')
finally:runner.Watch,runner.preflight=original_watch,original_preflight
# Git queries must propagate a bounded timeout.
original_git=runner.subprocess.check_output
def timeout_git(*args,**kwargs):
 if kwargs.get('timeout')!=30:raise RuntimeError('Git query lacks 30-second timeout')
 raise runner.subprocess.TimeoutExpired(args[0],kwargs['timeout'])
runner.subprocess.check_output=timeout_git
try:
 try:runner.git_query('rev-parse','HEAD')
 except runner.subprocess.TimeoutExpired:pass
 else:raise RuntimeError('Git timeout was ignored')
finally:runner.subprocess.check_output=original_git
original_pin=runner.PLAN_PIN;runner.PLAN_PIN='0'*64
try:
 try:runner.preflight()
 except runner.Refusal as e:
  if 'pin drift' not in str(e):raise
 else:raise RuntimeError('bad plan pin accepted')
finally:runner.PLAN_PIN=original_pin
spec=importlib.util.spec_from_file_location('coherent_monitor_control',P/'monitor.py');monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
with tempfile.TemporaryDirectory(prefix='coherent490-control-',dir='/tmp') as td:
 # Initial owned state exists before any later pin hashing can fail.
 own=Path(td)/'owned-output';initial=runner.create_owned_state(own)
 if json.loads((own/'state.json').read_text())['status']!='STARTING':raise RuntimeError('initial state missing')
 class StopWatch:
  def check(self):raise runner.Refusal('synthetic watchdog trip')
 runner.ACTIVE_WATCH=StopWatch()
 try:
  try:runner.sha(P/'plan.json')
  except runner.Refusal as e:
   runner.mark_failed(initial,e,0);runner.write_state(own,initial)
  else:raise RuntimeError('watchdog did not stop hashing')
  if json.loads((own/'state.json').read_text())['status']!='FAILED':raise RuntimeError('initial failure not recorded')
  # The failure receipt path must hash/save child results even after watchdog trip.
  log=Path(td)/'synthetic-child.log';log.write_text('captured child output')
  row={};saved=[]
  def save(*,force=False):
   if not force:raise RuntimeError('child receipt not forced')
   saved.append(True)
  runner.record_child_result(row,'compile',{'exit':-15,'stop_reason':'disk_floor'},log,save)
  if not saved or row['compile']['exit']!=-15 or 'log_sha256' not in row['compile']:raise RuntimeError('child-stop receipt lost')
 finally:runner.ACTIVE_WATCH=None
 log=Path(td)/'owned-control.log';res=monitor.run([sys.executable,'-I','-S','-B','-c','import time;time.sleep(30)'],Path(td),os.environ.copy(),log,rss_limit=4*1024**3,mem_floor=1,disk_floor=10**30,seconds=5,interval=.1)
 if res['stop_reason']!='disk_floor' or res['exit'] in (None,0) or res['monitor_errors'] or res['observed_descendant_pids']:raise RuntimeError('disk-stop control failed '+repr(res))
print(json.dumps({'status':'PASS_NON_LEAN_CONTROLS','existing_output_refused':True,'bad_plan_pin_refused':True,'watchdog_active_during_initial_preflight':True,'git_timeout_propagated':True,'initial_failure_recorded':True,'child_stop_receipt_preserved':True,'synthetic_monitor_stop':res['stop_reason'],'monitor_child_exit':res['exit'],'scope':'No Lean; only an owned temporary test process/directory. No preexisting files removed.'},sort_keys=True))
