#!/usr/bin/env python3
"""Supervise a capped compiled-header survey; no project module is built."""
import hashlib
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
inventory=here.parent/'compiled-header-inventory/inventory.py'
reader=here.parent/'compiled-header-inventory/stream_imports.lean'
policy=here/'policy.json'; direct=here/'direct-result.json'
result=here/'header-result.json';log=here/'header.log';receipt=here/'header-observation.json'
if any(os.path.lexists(p) for p in (result,log,receipt)):raise SystemExit('refusing existing output')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
inputs={str(p):sha(p) for p in (inventory,reader,policy,direct,Path(__file__))}
d=json.loads(direct.read_text())
if d['status']!='PASS_DIRECT_DEPS_NOT_IMPORT_CHECK':raise RuntimeError('direct probe not passed')
seeds=sorted(k for k in d['selected'] if k!='Init')
if len(seeds)!=24:raise RuntimeError('expected 22 new imports and two Matrix probes')
def available():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
    raise RuntimeError('MemAvailable missing')
def group_rss(group):
    total=0;members=[]
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit():continue
        try:
            stat=(proc/'stat').read_text().rsplit(')',1)[1].split()
            if int(stat[2])!=group or stat[0]=='Z':continue
            rss=[int(x.split()[1])*1024 for x in (proc/'status').read_text().splitlines() if x.startswith('VmRSS:')]
            if len(rss)!=1:raise RuntimeError('RSS missing '+proc.name)
            total+=rss[0];members.append(int(proc.name))
        except (FileNotFoundError,ProcessLookupError):continue
    return total,members
if available()<10*1024**3:raise RuntimeError('MemAvailable below launch floor')
cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',sys.executable,'-I','-S','-B',str(inventory),
     '--policy',str(policy),'--output',str(result),'--max-modules','64','--bytes-per-second',str(16*1024**2)]
for name in seeds:cmd.extend(['--seed',name])
start=time.monotonic();samples=[];reason=None
with log.open('x') as f:
    p=subprocess.Popen(cmd,stdin=subprocess.DEVNULL,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
    while p.poll() is None:
        mem=available();rss,members=group_rss(p.pid)
        samples.append({'seconds':round(time.monotonic()-start,2),'available':mem,'group_rss':rss,'members':members})
        if mem<10*1024**3:reason='available memory below 10 GiB'
        elif rss>=7*1024**3//2:reason='process-group RSS at or above 3.5 GiB'
        elif time.monotonic()-start>=60:reason='60-second timeout'
        if reason:
            try:os.killpg(p.pid,signal.SIGTERM)
            except ProcessLookupError:pass
            break
        time.sleep(.25)
    try:code=p.wait(timeout=5)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid,signal.SIGKILL);code=p.wait();reason=reason or 'forced termination'
after={str(p):sha(p) for p in (inventory,reader,policy,direct,Path(__file__))}
record={'exit':code,'stop_reason':reason,'seconds':round(time.monotonic()-start,3),
        'samples':samples,'command':cmd,'input_hashes_before':inputs,'input_hashes_after':after,
        'inputs_stable':inputs==after,'result_exists':result.is_file(),
        'result_sha256':sha(result) if result.is_file() else None,'log_sha256':sha(log),
        'scope':'Capped compiled-header traversal; no project build or combined import proof.'}
receipt.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps(record,sort_keys=True))
if code or reason or inputs!=after or not result.is_file():raise SystemExit(1)
