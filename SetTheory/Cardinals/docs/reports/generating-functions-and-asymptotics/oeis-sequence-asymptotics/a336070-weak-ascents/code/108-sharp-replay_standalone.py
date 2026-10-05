#!/usr/bin/env python3
"""Reproduce the complete exact package from an isolated, enumerated file copy."""
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory
HERE=Path(__file__).resolve().parent
FILES=('verify_exact.py','fixtures.json','expected_summary.json','run_checks.py','weak_verify_exact.py','weak_fixtures.json','weak_expected_summary.json','weak_run_checks.py')

def require(ok,message):
    if not ok: raise RuntimeError(message)

def main():
    hashes={name:sha256((HERE/name).read_bytes()).hexdigest() for name in FILES}
    runs=[]
    with TemporaryDirectory(prefix='standalone-',dir=HERE) as td:
        dest=Path(td)
        for name in FILES: shutil.copy2(HERE/name,dest/name)
        require(sorted(p.name for p in dest.iterdir())==sorted(FILES),'unexpected files in fresh directory')
        for argv in ([sys.executable,'verify_exact.py'],[sys.executable,'-O','verify_exact.py'],[sys.executable,'run_checks.py']):
            cp=subprocess.run(argv,cwd=dest,capture_output=True,text=True,timeout=900)
            require(cp.returncode==0,'standalone replay failed: '+cp.stderr)
            payload=json.loads(cp.stdout)
            require(payload.get('status')=='passed','standalone verifier/campaign did not pass')
            runs.append({'command':argv[1:],'returncode':cp.returncode,'status':payload['status']})
        campaign=json.loads((dest/'corruption_results.json').read_text())
        require(campaign['weak_campaign_rerun'] is True,'fresh replay did not rerun weighted campaign')
        for name in FILES: require(sha256((dest/name).read_bytes()).hexdigest()==hashes[name],'replay changed '+name)
        result={'schema':'report108-standalone-replay-v1','status':'passed','scope':'Finite exact checks and corruption detection, not analytic proof.','fresh_directory_initial_files':list(FILES),'input_sha256':hashes,'runs':runs,'combined_independent_mutations':campaign['combined_independent_mutations'],'combined_failed_corrupt_runs':campaign['combined_failed_corrupt_runs'],'network_or_external_package_required':False,'original_input_files_unchanged':True}
    for name in FILES: require(sha256((HERE/name).read_bytes()).hexdigest()==hashes[name],'original input changed '+name)
    (HERE/'standalone_replay.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,sort_keys=True))
    return 0
if __name__=='__main__':
    try: sys.exit(main())
    except Exception as error:
        print(json.dumps({'status':'failed','error_type':type(error).__name__,'error':str(error)},sort_keys=True),file=sys.stderr);sys.exit(1)
