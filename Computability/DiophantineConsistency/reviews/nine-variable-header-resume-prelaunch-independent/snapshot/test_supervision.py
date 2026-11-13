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
    for mode in ('monitor_exception','leader_exit','timeout'):
        marker=base/(mode+'.pids');log=base/(mode+'.log')
        def hook(members):
            if mode=='monitor_exception' and marker.exists() and len(members)>=3:
                raise RuntimeError('synthetic monitor failure')
        r=module.supervise([sys.executable,'-I','-S','-B','-c',leader,str(marker),mode,child],log,
             cwd=base,env=dict(os.environ),timeout_seconds=1 if mode=='timeout' else 5,
             mem_floor=0,disk_floor=0,monitor_hook=hook)
        require(marker.is_file(),'descendant marker missing '+mode)
        child_pid,grandchild_pid=map(int,marker.read_text().split())
        require(r['drained'] and r['drain_error'] is None and not module.group_members(r['session_id']),
                'owned session failed to drain '+mode)
        require(not Path('/proc',str(child_pid)).exists() and not Path('/proc',str(grandchild_pid)).exists(),
                'descendants were not both terminated and reaped '+mode)
        require(any(len(s['members'])>=3 for s in r['samples']) or mode=='leader_exit',
                'child/grandchild were not sampled '+mode)
        if mode=='monitor_exception':require(r['reason'].startswith('monitor exception:'),'exception not recorded')
        elif mode=='leader_exit':require(r['reason']=='leader exited with live owned descendants' and
                                       bool(r['leftover_at_exit']),'descendants not detected')
        else:require(r['reason']=='timeout','timeout not recorded')
        results.append({'mode':mode,'reason':r['reason'],'drained':r['drained'],
                        'child_pid':child_pid,'grandchild_pid':grandchild_pid,
                        'sample_count':len(r['samples'])})
print(json.dumps({'status':'PASS_SYNTHETIC_SUPERVISION_CONTROLS','cases':results,
 'scope':'Owned Python child/grandchild cleanup controls only; no Lean or header traversal.'},sort_keys=True))
