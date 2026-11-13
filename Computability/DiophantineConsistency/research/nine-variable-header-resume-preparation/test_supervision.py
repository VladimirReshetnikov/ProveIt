#!/usr/bin/env python3
"""Synthetic owned-session failure controls; launches no Lean process."""
import importlib.util
import json
import os
import sys
import tempfile
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('owned_supervision',here/'supervision.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
child='''import os,subprocess,sys,time
os.setpgid(0,0)
p=subprocess.Popen([sys.executable,"-I","-S","-B","-c","import time;time.sleep(30)"])
open(sys.argv[1],"w").write(str(os.getpid())+" "+str(p.pid))
time.sleep(30)
'''
leader='''import pathlib,subprocess,sys,time
marker=sys.argv[1];mode=sys.argv[2]
subprocess.Popen([sys.executable,"-I","-S","-B","-c",sys.argv[3],marker])
while not pathlib.Path(marker).exists():time.sleep(.01)
if mode=="leader_exit":sys.exit(0)
time.sleep(30)
'''
def require(ok,msg):
    if not ok:raise RuntimeError(msg)
results=[]
with tempfile.TemporaryDirectory(prefix='header-resume-supervision-controls-') as temp:
    base=Path(temp)
    for mode in ('monitor_exception','leader_exit','timeout','signal_error'):
        marker=base/(mode+'.pids');log=base/(mode+'.log')
        def hook(members):
            if mode=='monitor_exception' and marker.exists() and len(members)>=3:
                raise RuntimeError('synthetic monitor failure')
        actual_kill=module.os.kill;failed=[];subsequent=[]
        def flaky_kill(pid,sig):
            if mode=='signal_error' and not failed:
                failed.append(pid);raise PermissionError('synthetic signal failure')
            if failed:subsequent.append(pid)
            return actual_kill(pid,sig)
        if mode=='signal_error':module.os.kill=flaky_kill
        try:
            r=module.supervise([sys.executable,'-I','-S','-B','-c',leader,str(marker),mode,child],log,
                 cwd=base,env=dict(os.environ),timeout_seconds=1 if mode in ('timeout','signal_error') else 5,
                 mem_floor=0,disk_floor=0,monitor_hook=hook)
        finally:module.os.kill=actual_kill
        require(marker.is_file(),'descendant marker missing '+mode)
        child_pid,grandchild_pid=map(int,marker.read_text().split())
        require(r['drained'] and (r['drain_error'] is None if mode!='signal_error' else
                r['drain_error'].startswith('member signal failed:')) and not module.group_members(r['session_id']),
                'owned session failed to drain '+mode)
        require(not Path('/proc',str(child_pid)).exists() and not Path('/proc',str(grandchild_pid)).exists(),
                'descendants were not both terminated and reaped '+mode)
        require(any(len(s['members'])>=3 for s in r['samples']) or mode=='leader_exit',
                'child/grandchild were not sampled '+mode)
        if mode=='monitor_exception':require(r['reason'].startswith('monitor exception:'),'exception not recorded')
        elif mode=='leader_exit':require(r['reason']=='leader exited with live owned descendants' and
                                       bool(r['leftover_at_exit']),'descendants not detected')
        else:require(r['reason']=='timeout','timeout not recorded')
        if mode=='signal_error':require(failed and any(pid!=failed[0] for pid in subsequent),
                                       'signal error aborted cleanup of other members')
        results.append({'mode':mode,'reason':r['reason'],'drained':r['drained'],
                        'drain_error':r['drain_error'],
                        'child_pid':child_pid,'grandchild_pid':grandchild_pid,
                        'sample_count':len(r['samples'])})
    # Inspection and fallback group signaling can both fail: retain failure,
    # then continue inspecting and signaling individually.
    old_group=module.group_members;old_kill=module.os.kill;old_killpg=module.os.killpg
    old_waitpid=module.os.waitpid;observed=[];calls=[]
    class Leader:
        pid=99999999
        def poll(self):return 0
    def groups(group,include_zombies=False):
        calls.append(1)
        if len(calls)==1:raise PermissionError('synthetic inspection failure')
        if len(calls)==2:return [{'pid':99999998,'state':'S','rss':0}]
        return []
    def denied(group,sig):raise PermissionError('synthetic group signal failure')
    try:
        module.group_members=groups;module.os.killpg=denied
        module.os.kill=lambda pid,sig:observed.append(pid)
        module.os.waitpid=lambda *args: (_ for _ in ()).throw(ChildProcessError())
        drained,error=module.drain(99999999,Leader())
        require(drained and error and observed==[99999998],'group signal error aborted cleanup')
    finally:
        module.group_members=old_group;module.os.kill=old_kill;module.os.killpg=old_killpg;module.os.waitpid=old_waitpid
    # Cleanup exceptions must not leave the supervisor's subreaper flag changed.
    old_flag=module.subreaper();old_drain=module.drain
    def drain_then_raise(group,leader):
        old_drain(group,leader)
        raise RuntimeError('synthetic drain exception')
    try:
        module.subreaper(0);module.drain=drain_then_raise
        try:
            module.supervise([sys.executable,'-I','-S','-B','-c','pass'],base/'subreaper.log',
                             cwd=base,env=dict(os.environ),mem_floor=0,disk_floor=0)
        except RuntimeError as exc:require('synthetic drain exception' in str(exc),'unexpected exception')
        else:raise RuntimeError('drain exception not propagated')
        require(module.subreaper()==0,'subreaper state not restored')
    finally:module.drain=old_drain;module.subreaper(old_flag)
print(json.dumps({'status':'PASS_SYNTHETIC_SUPERVISION_CONTROLS','cases':results,
 'group_signal_failure_continued':True,'subreaper_restored_after_drain_exception':True,
 'scope':'Owned Python child/grandchild cleanup controls only; no Lean or header traversal.'},sort_keys=True))
