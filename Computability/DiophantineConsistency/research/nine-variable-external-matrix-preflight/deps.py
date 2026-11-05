#!/usr/bin/env python3
"""Bounded lean --deps path probe; this does not import/elaborate a client."""
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
survey=here.parent/'nine-variable-current-base-source-survey/result-final.json'
probe=here/'DirectExternalProbe.lean'
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
roots=[Path('/tmp/current14-standard-fresh-build-20261104/lib'),
       Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),
       Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean',
          '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
    if not ok:raise RuntimeError(msg)
require(sha(survey)=='7aa788ec612ef2d1cf40e65cf16b507099532477cd581dfe2c560d7b934d31ca','survey drift')
require(sha(lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','Lean drift')
names=json.loads(survey.read_text())['new_declared_external']
matrix=['Foundation.Vorspiel.Matrix','Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber']
names=names+matrix
source=probe.read_text();declared=re.findall(r'^import ([A-Za-z0-9_.]+)$',source,re.M)
require(declared==names and len(names)==24 and len(set(names))==24,'probe import mismatch')
def inspect():
    result={}
    for module in names+['Init']:
        stem=Path(*module.split('.'))
        for root in roots:
            for suffix in suffixes:
                p=root/(str(stem)+suffix)
                if os.path.lexists(p):
                    require(p.is_file(),'invalid companion '+str(p))
                    st=p.stat();result[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p),
                                                'size':st.st_size,'mtime_ns':st.st_mtime_ns}
                else:result[str(p)]=None
    return result
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
            require(len(rss)==1,'RSS missing '+proc.name);total+=rss[0];members.append(int(proc.name))
        except (FileNotFoundError,ProcessLookupError):continue
    return total,members
before=inspect(); input_hashes={'probe':sha(probe),'survey':sha(survey),'lean':sha(lean),'runner':sha(Path(__file__))}
require(available()>=10*1024**3,'MemAvailable below launch floor')
env=dict(os.environ,LEAN_PATH=str(roots[0])+':'+str(roots[1]),LEAN_NUM_THREADS='1')
for k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(k,None)
cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(lean),'-j1','--deps',str(probe)]
start=time.monotonic(); samples=[];reason=None
p=subprocess.Popen(cmd,env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                   text=True,start_new_session=True)
while p.poll() is None:
    mem=available();rss,members=group_rss(p.pid)
    samples.append({'available':mem,'group_rss':rss,'members':members})
    if mem<10*1024**3:reason='available memory below 10 GiB'
    elif rss>=7*1024**3//2:reason='process-group RSS at or above 3.5 GiB'
    elif time.monotonic()-start>=60:reason='60-second timeout'
    if reason:
        try:os.killpg(p.pid,signal.SIGTERM)
        except ProcessLookupError:pass
        break
    time.sleep(.2)
try:stdout,stderr=p.communicate(timeout=5)
except subprocess.TimeoutExpired:
    os.killpg(p.pid,signal.SIGKILL);stdout,stderr=p.communicate();reason=reason or 'forced termination'
after=inspect()
require(before==after and input_hashes=={'probe':sha(probe),'survey':sha(survey),'lean':sha(lean),'runner':sha(Path(__file__))},'input/companion drift')
require(p.returncode==0 and reason is None and not stderr,'lean --deps failed: '+repr((p.returncode,reason,stderr)))
selected={};counts={}
for line in stdout.splitlines():
    path=Path(line);require(path.is_absolute() and path.is_file(),'invalid reported path '+line)
    possible=[(i,root) for i,root in enumerate(roots) if path.is_relative_to(root)]
    require(len(possible)==1,'dependency outside roots or overlapping '+line)
    i,root=possible[0];rel=path.relative_to(root)
    require(str(rel).endswith('.olean'),'unexpected dependency suffix '+line)
    module=str(rel)[:-6].replace('/','.');require(module in names+['Init'],'unexpected module '+module)
    counts[module]=counts.get(module,0)+1
    require(module not in selected or selected[module]['path']==line,'conflicting duplicate provider '+module)
    selected[module]={'path':line,'realpath':str(path.resolve()),'sha256':sha(path),'root':i}
require(set(selected)==set(names+['Init']),'declared dependency set mismatch')
require(all(v==1 or (k=='Init' and v==2) for k,v in counts.items()),'unexpected duplicate deps')
collisions=[]
for module in names+['Init']:
    stem=str(Path(*module.split('.')))+'.olean'
    choices=[before[str(root/stem)] for root in roots if before[str(root/stem)] is not None]
    if len(choices)>1:
        collisions.append({'module':module,'choices':choices,'different_hashes':len({c['sha256'] for c in choices})>1})
print(json.dumps({'status':'PASS_DIRECT_DEPS_NOT_IMPORT_CHECK','command':cmd,'exit':p.returncode,
 'seconds':round(time.monotonic()-start,3),'samples':samples,'guard_entries':len(before),
 'guards_before':before,'guards_after':after,'selected':selected,'counts':counts,'collisions':collisions,
 'inputs':input_hashes,'scope':'lean --deps resolves only these direct imports; no combined import load, package-transitive closure, or project build'},sort_keys=True))
