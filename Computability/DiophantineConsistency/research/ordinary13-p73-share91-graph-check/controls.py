#!/usr/bin/env python3
"""Non-Lean guard/receipt/monitor controls; uses only owned temporary files."""
import importlib.util
import json
import os
import sys
import tempfile
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('p73_runner_control',P/'run.py')
runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
runner.self_test()

# An existing output path and a bad pin must be refused before any resource
# or Lean action, including when the filesystem is below the stop floor.
original=runner.OUT;runner.OUT=P
try:
    try: runner.preflight()
    except runner.Refusal as e:
        if 'output already exists' not in str(e): raise
    else: raise RuntimeError('preexisting output accepted')
finally: runner.OUT=original
old=runner.PINS[runner.PLAN];runner.PINS[runner.PLAN]='0'*64
try:
    try: runner.preflight()
    except runner.Refusal as e:
        if 'pin drift' not in str(e): raise
    else: raise RuntimeError('bad plan pin accepted')
finally: runner.PINS[runner.PLAN]=old

# A real run and an explicit preflight both start the resource watchdog first.
old_watch,old_preflight=runner.Watch,runner.preflight;observed={}
class ProbeWatch:
    def __init__(self,start): self.started=False;self.stopped=False;observed['watch']=self
    def begin(self): self.started=True
    def check(self): pass
    def stop(self): self.stopped=True
def reject_preflight(*args,**kwargs):
    if not isinstance(runner.ACTIVE_WATCH,ProbeWatch) or not runner.ACTIVE_WATCH.started:
        raise RuntimeError('preflight entered before watchdog')
    raise runner.Refusal('synthetic preflight refusal')
runner.Watch,runner.preflight=ProbeWatch,reject_preflight
try:
    for action in (runner.run,runner.guarded_preflight):
        try: action()
        except runner.Refusal as e:
            if 'synthetic preflight refusal' not in str(e): raise
        else: raise RuntimeError('synthetic refusal ignored')
        if not observed['watch'].stopped or runner.ACTIVE_WATCH is not None:
            raise RuntimeError('watchdog not cleaned up')
finally: runner.Watch,runner.preflight=old_watch,old_preflight

# Git queries have a finite timeout and do not silently swallow it.
old_git=runner.subprocess.check_output
def timeout_git(*args,**kwargs):
    if kwargs.get('timeout') != 30: raise RuntimeError('Git timeout absent')
    raise runner.subprocess.TimeoutExpired(args[0],kwargs['timeout'])
runner.subprocess.check_output=timeout_git
try:
    try: runner.git_query('rev-parse','HEAD')
    except runner.subprocess.TimeoutExpired: pass
    else: raise RuntimeError('Git timeout ignored')
finally: runner.subprocess.check_output=old_git

spec=importlib.util.spec_from_file_location('p73_monitor_control',runner.MON)
monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
with tempfile.TemporaryDirectory(prefix='p73-guard-control-',dir='/tmp') as td:
    own=Path(td)/'owned';initial=runner.create_owned_state(own)
    if json.loads((own/'state.json').read_text())['status']!='STARTING': raise RuntimeError('initial state missing')
    try: runner.create_owned_state(own)
    except FileExistsError: pass
    else: raise RuntimeError('owned output was overwritten')
    class StopWatch:
        def check(self): raise runner.Refusal('synthetic watchdog trip')
    runner.ACTIVE_WATCH=StopWatch()
    try:
        try: runner.sha(P/'plan.json')
        except runner.Refusal as e:
            runner.mark_failed(initial,e,0);runner.write_state(own,initial)
        else: raise RuntimeError('watchdog did not stop hashing')
        if json.loads((own/'state.json').read_text())['status']!='FAILED': raise RuntimeError('initial failure not recorded')
        log=Path(td)/'synthetic-child.log';log.write_text('captured child output')
        row={};saved=[]
        def save(*,force=False):
            if not force: raise RuntimeError('child receipt not forced')
            saved.append(True)
        runner.record_child_result(row,'compile',{'exit':-15,'stop_reason':'disk_floor'},log,save)
        if not saved or row['compile']['exit']!=-15 or 'log_sha256' not in row['compile']:
            raise RuntimeError('child stop receipt lost')
    finally: runner.ACTIVE_WATCH=None
    log=Path(td)/'synthetic-monitor.log'
    result=monitor.run([sys.executable,'-I','-S','-B','-c','import time;time.sleep(30)'],Path(td),os.environ.copy(),log,
                       rss_limit=4*1024**3,mem_floor=1,disk_floor=10**30,seconds=5,interval=.1)
    if result['stop_reason']!='disk_floor' or result['exit'] in (None,0) or result['monitor_errors'] or result['observed_descendant_pids']:
        raise RuntimeError('synthetic disk stop failed '+repr(result))
print(json.dumps({'status':'PASS_NON_LEAN_CONTROLS','preexisting_output_refused':True,'bad_plan_pin_refused':True,
                  'watchdog_before_run_and_preflight':True,'git_timeout_propagated':True,'initial_failure_recorded':True,
                  'child_stop_receipt_preserved':True,'synthetic_monitor_stop':result['stop_reason'],
                  'synthetic_child_exit':result['exit'],
                  'scope':'No Lean; only an owned temporary test process and directory. No preexisting files removed.'},sort_keys=True))
