#!/usr/bin/env python3
"""Fresh standalone Coq/Rocq check of DirectInfinity.v (POSIX/WSL Python)."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
sha = lambda x: hashlib.sha256(x).hexdigest()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--coqc', default='coqc')
    p.add_argument('--coqchk', default='coqchk')
    p.add_argument('--out', required=True, type=Path)
    args = p.parse_args()
    out = args.out.resolve(); out.mkdir(parents=True,exist_ok=False)
    manifest = json.loads((HERE/'source_provenance.json').read_text())
    source = (HERE/'DirectInfinity.v').read_bytes()
    if sha(source) != manifest['rocq_source_sha256']:
        raise SystemExit('DirectInfinity.v differs from the reviewed source')
    (out/'DirectInfinity.v').write_bytes(source)
    env = dict(os.environ); env['COQPATH'] = ''
    bins = {n:Path(shutil.which(getattr(args,n))).resolve() for n in ('coqc','coqchk')}
    version=subprocess.check_output([str(bins['coqc']),'--version'],env=env,text=True)
    receipt={'status':'RUNNING','scope':'standalone direct-Infinity mathematical core',
             'version':version,'source_sha256':sha(source),'checks':[],
             'driver_sha256':sha(Path(__file__).read_bytes()),
             'source_manifest_sha256':sha((HERE/'source_provenance.json').read_bytes()),
             'project_objects_reused':False,'repository_imports':False,
             'formseed_adapter_instantiated':False,'full_tm_endpoint_rebuilt':False,
             'compiler_sha256':sha(bins['coqc'].read_bytes()),
             'kernel_checker_sha256':sha(bins['coqchk'].read_bytes())}
    def save(): (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    def run(n,argv):
        start=time.monotonic()
        result=subprocess.run([str(bins[n]),*argv],cwd=out,env=env,
                              stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        logfile=n+'.log';(out/logfile).write_bytes(result.stdout)
        receipt['checks'].append({'program':n,'arguments':argv,'exit_code':result.returncode,
            'seconds':time.monotonic()-start,'log':logfile,'log_sha256':sha(result.stdout)})
        if result.returncode:
            receipt['status']='FAIL';save();print(result.stdout.decode(errors='replace'));raise SystemExit(result.returncode)
        save();return result.stdout.decode(errors='replace')
    save()
    with open('/tmp/proveit-k215-proof-build.lock','a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        output=run('coqc',['-q','DirectInfinity.v'])
        reports=output.count('Closed under the global context')
        receipt['closed_assumption_reports']=reports
        if reports!=8 or 'Axioms:' in output:
            receipt['status']='FAIL';save();raise SystemExit('Unexpected assumption audit')
        run('coqchk',['-o','DirectInfinity'])
    receipt['status']='PASS';save()
    print('PASS: eight closed reports; fresh compilation; recursive kernel check')

if __name__=='__main__': main()
