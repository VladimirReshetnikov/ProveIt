#!/usr/bin/env python3
"""Compile the Rocq command factorization against exact pinned repository sources.

No precompiled project objects are reused. The only Coq 8.x compatibility edit
is the Stdlib -> Coq import prefix in disposable copies. The source provenance
manifest binds all inputs before any compiler is invoked.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
BASE = 'Computability/BusyBeaver/Research/ZFC/k225-formal/'
sha = lambda x: hashlib.sha256(x).hexdigest()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', required=True, type=Path)
    p.add_argument('--coqc', default='coqc')
    p.add_argument('--coqchk', default='coqchk')
    p.add_argument('--out', required=True, type=Path)
    args = p.parse_args()
    repo, out = args.repo.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out/'logs').mkdir()
    manifest = json.loads((HERE/'source_provenance.json').read_text())
    sources = manifest['sources']
    env = dict(os.environ); env['COQPATH'] = ''
    version = subprocess.check_output([args.coqc,'--version'], env=env, text=True)
    compat = bool(re.search(r'\bversion 8\.',version))
    receipt = {'base_commit':manifest['base_commit'], 'scope':'exact codec/command adapter only',
               'version':version, 'status':'RUNNING', 'sources':[], 'checks':[],
               'full_tm_endpoint_rebuilt':False, 'stdlib_to_coq_compatibility':compat,
               'project_objects_reused':False}
    for source in sources:
        src = (repo/source['path']) if source['repository'] else (HERE/source['path'])
        data=src.read_bytes()
        if sha(data)!=source['sha256']:
            raise SystemExit('Unexpected source bytes: '+str(src))
        compiled=data.replace(b'From Stdlib ',b'From Coq ') if compat else data
        dest=out/(source['module'].replace('.','/')+'.v')
        dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(compiled)
        receipt['sources'].append({**source,'compiled_sha256':sha(compiled)})
    flags=['-Q','K230S','K230S','-Q','K230L','K230L','-Q','K215F','K215F']
    def save():
        (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    def run(name,command):
        start=time.monotonic()
        r=subprocess.run(command,cwd=out,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log='logs/'+name+'.log'; (out/log).write_bytes(r.stdout)
        receipt['checks'].append({'name':name,'exit_code':r.returncode,
           'seconds':time.monotonic()-start,'log':log,'log_sha256':sha(r.stdout)})
        print(name,r.returncode,flush=True)
        if r.returncode:
            receipt['status']='FAIL';save();print(r.stdout.decode(errors='replace'));raise SystemExit(r.returncode)
        save();return r.stdout.decode(errors='replace')
    save()
    with open('/tmp/proveit-k215-proof-build.lock','a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        for source in sources:
            name=source['module']
            output=run(name,[args.coqc,'-q',*flags,name.replace('.','/')+'.v'])
            if name=='CommandFactor':
                n=output.count('Closed under the global context')
                receipt['closed_adapter_assumption_reports']=n
                if n!=7 or 'Axioms:' in output:
                    receipt['status']='FAIL';save();raise SystemExit('Unexpected assumptions')
        run('coqchk',[args.coqchk,*flags,'CommandFactor'])
    receipt['status']='PASS';save()
    print('PASS: fresh exact-source component build and recursive kernel check')

if __name__=='__main__':
    main()
