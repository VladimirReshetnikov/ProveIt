#!/usr/bin/env python3
"""Synthetic owned-session checks with short Python children, never Lean."""
import hashlib,importlib.util,json,os,sys,tempfile
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent;helper=here/'owned.py'
if hashlib.sha256(helper.read_bytes()).hexdigest()!='a41aee499bcef7b6ece79e1e7eae2b99210a70c1dafc1e54f2de55fbfc8d6201':raise RuntimeError('helper mismatch')
spec=importlib.util.spec_from_file_location('owned_test',helper);owned=importlib.util.module_from_spec(spec);spec.loader.exec_module(owned)
def gone(pid):
 try:os.kill(pid,0)
 except ProcessLookupError:return True
 return False
results={}
with tempfile.TemporaryDirectory(prefix='normalized106-owned-test-') as tmp:
 for mode in ('success','resource_stop','monitor_exception'):
  seen=[];reports=[];reaped=[]
  def monitor(pid):
   seen.append(pid)
   if mode=='monitor_exception':raise RuntimeError('synthetic monitor exception')
   return mode!='resource_stop'
  command=[sys.executable,'-I','-S','-B','-c','import time; time.sleep(0.35)']
  with open(os.path.join(tmp,mode+'.log'),'wb') as log:
   try:
    code,elapsed,life=owned.run(command,cwd=tmp,env=dict(os.environ),stdout=log,stderr=log,timeout=3,disk_check=monitor,report=reports.append,poll_interval=.05,grace=.2,on_reap=lambda code,life:reaped.append((code,life)))
    if mode!='success' or code!=0 or not life['session_drained'] or not life['direct_child_reaped']:raise RuntimeError('unexpected owned success')
    pid=life['pid'];outcome='SUCCESS_REAPED'
   except RuntimeError as exc:
    if mode=='success' or not seen:raise
    pid=seen[0]
    if mode=='resource_stop' and not any(x in str(exc) for x in ('stopped by time/free-space bound','finished outside resource bounds')):raise
    if mode=='monitor_exception' and 'synthetic monitor exception' not in str(exc):raise
    outcome='REJECTED_REAPED'
  if not seen or not gone(pid):raise RuntimeError(('owned child survived',mode,pid))
  if len(reaped)!=1 or reaped[0][1]['pid']!=pid or not reaped[0][1]['direct_child_reaped']:raise RuntimeError(('missing reap receipt',mode))
  if mode=='resource_stop' and not any('SIGTERM' in x for x in reports):raise RuntimeError('missing resource-stop signal')
  if mode=='monitor_exception' and not any('MONITOR_FAILURE_WAITING' in x for x in reports):raise RuntimeError('missing passive-wait report')
  child_code=reaped[0][0]
  if mode in ('success','monitor_exception') and child_code!=0:raise RuntimeError(('unexpected child exit',mode,child_code))
  if mode=='resource_stop' and child_code not in (-15,-9):raise RuntimeError(('unexpected stopped exit',child_code))
  results[mode]={'outcome':outcome,'actual_child_exit':child_code}
print(json.dumps({'status':'PASS_SYNTHETIC_OWNED_SESSION_CONTROLS','cases':results,'scope':'Three short Python-child tests; no Lean or actual import probe.'},sort_keys=True))
