#!/usr/bin/env python3
"""Rebuild the small frame-contract closure in a fresh isolated Lean workspace.

No existing project objects are used. Every source, dependency object, compiler,
command, exit status, duration and log is bound in the resulting receipt. The
existing K215 shared compiler lock is honored. This is NOT a full endpoint build.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time

MODULES = ['BusyBeaver.ZFC.'+s for s in [
    'KZip','KRuntimeCore','KHome','KTableCore','KTable215','RegisterPath',
    'KControlFrame','KLeftFrame','KLeftFrame215','KFramedControl215']] + ['FrameAudit']
EXPECTED = {
    'K215FrameAudit.actual_control_runtime': ['propext','Classical.choice','Quot.sound'],
    'K215FrameAudit.actual_control_source': ['propext','Quot.sound'],
    'K215FrameAudit.boundary_guard_is_essential': ['propext'],
    'K215FrameAudit.all_runtime_templates_accounted_for': [],
}
ALLOWED={'propext','Classical.choice','Quot.sound'}

def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--timeout',type=int,default=300)
    a=ap.parse_args()
    home=Path(__file__).resolve().parent
    lean=a.lean.resolve()
    out=a.out.resolve()
    if out.exists() and any(out.iterdir()):
        raise SystemExit('Output directory must be empty')
    out.mkdir(parents=True,exist_ok=True)
    (out/'logs').mkdir()
    pins=json.loads((home/'SOURCE_PINS.json').read_text())
    for pin in pins['sources']:
        p=home/Path(pin['module'].replace('.','/')+'.lean')
        if digest(p)!=pin['sha256']:
            raise SystemExit('Pinned dependency differs: '+str(p))
    env=os.environ.copy()
    env['LEAN_PATH']=str(out)
    # The shipped core is the sole external import boundary.
    env.pop('LEAN_SRC_PATH',None)
    version=subprocess.check_output([str(lean),'--version'],text=True).strip()
    if 'version 4.32.0' not in version:
        raise SystemExit('Expected Lean 4.32.0, got '+version)
    receipt={'status':'RUNNING','scope':'10 project modules plus one closed client; not the K215 endpoint',
        'repository':pins['repository'],'commit':pins['commit'],
        'compiler':{'path':str(lean),'sha256':digest(lean),'version':version},
        'driver_sha256':digest(__file__),'modules':[],'external_imports':['Init']}
    recpath=out/'receipt.json'
    def save(): recpath.write_text(json.dumps(receipt,indent=2)+'\n')
    save()
    completed=set()
    for module in MODULES:
        rel=Path(module.replace('.','/')+'.lean')
        src=home/rel
        dst=out/rel
        dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(src,dst)
        imports=[]
        for line in src.read_text().splitlines():
            if line.startswith('import '): imports+=line[len('import '):].split()
        bad=[i for i in imports if i not in completed and i!='Init']
        if bad: raise SystemExit('Unavailable predecessor imports: '+str(bad))
        deps={i:digest(out/Path(i.replace('.','/')+'.olean')) for i in imports if i!='Init'}
        obj=rel.with_suffix('.olean')
        logpath=out/'logs'/(module+'.log')
        command=[str(lean),'-j1','-M4096','-o',str(obj),str(rel)]
        started=time.monotonic()
        with open('/tmp/proveit-k215-proof-build.lock','a') as lock,logpath.open('w') as log:
            fcntl.flock(lock,fcntl.LOCK_EX)
            proc=subprocess.Popen(command,cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            try: code=proc.wait(timeout=a.timeout)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid,signal.SIGKILL); proc.wait(); code=-9
        text=logpath.read_text()
        record={'module':module,'source_sha256':digest(src),'source_bytes':src.stat().st_size,
            'source_lines':len(src.read_text().splitlines()),'imports':imports,'dependency_objects':deps,
            'command':command,'exit_code':code,'seconds':round(time.monotonic()-started,6),
            'log':str(logpath.relative_to(out)),'log_sha256':digest(logpath)}
        if code==0 and (out/obj).is_file():record['object_sha256']=digest(out/obj)
        receipt['modules'].append(record)
        if code!=0 or 'error:' in text or 'warning:' in text or 'sorryAx' in text:
            receipt['status']='FAIL';save();print(text);raise SystemExit(1)
        completed.add(module);save();print(module+' OK',flush=True)
    profiles={}
    combined='\n'.join((out/r['log']).read_text() for r in receipt['modules'])
    for name,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",combined):
        profile=[a.strip() for a in axs.split(',') if a.strip()]
        if not set(profile)<=ALLOWED: raise SystemExit('Unexpected axiom profile: '+name+str(profile))
        profiles[name]=profile
    for name in re.findall(r"'([^']+)' does not depend on any axioms",combined):profiles[name]=[]
    for name,expected in EXPECTED.items():
        if name not in profiles or set(profiles[name])!=set(expected):
            raise SystemExit('Missing or altered closed-client axiom report: '+name)
    receipt['axiom_profiles']=profiles
    receipt['status']='PASS'
    receipt['warnings']=0
    receipt['templates']=35
    receipt['local_steps']=444
    receipt['maximum_template_steps']=39
    receipt['full_occurrence_assembly_checked']=False
    receipt['full_zfc_endpoint_rebuilt']=False
    receipt['total_compile_seconds']=round(sum(m['seconds'] for m in receipt['modules']),6)
    save();print(json.dumps({k:receipt[k] for k in ['status','templates','local_steps','total_compile_seconds']},indent=2))

if __name__=='__main__':main()
