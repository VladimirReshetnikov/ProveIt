"""Portable full replay. Python 3.10+ standard library only; no network use."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parent

def verify_manifest():
    count=0
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1)
        p=ROOT/name
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=digest:
            raise RuntimeError('Manifest mismatch: '+name)
        count+=1
    return count

def run():
    count=verify_manifest();runs=[]
    commands=[('producer CA',[],'compiler/check_five_binary.py'),
              ('producer frontend',[],'compiler/check_frontend.py'),
              ('all-input source verifier',[],'compiler/source-replay/verify_source.py'),
              ('normal and optimized independent audits',[],'compiler/audit_regression_modes.py'),
              ('normal API boundaries',[],'compiler/audit_api_independent.py'),
              ('optimized API boundaries',['-O'],'compiler/audit_api_independent.py'),
              ('report fixture identity',[],'verification/check_report_fixtures.py')]
    for title,flags,name in commands:
        print('Running '+title,flush=True)
        result=subprocess.run([sys.executable,*flags,str(ROOT/name)],cwd=ROOT/'compiler',capture_output=True,text=True)
        if result.returncode:
            print(result.stdout);print(result.stderr,file=sys.stderr)
            raise RuntimeError(title+' failed')
        runs.append({'check':title,'status':'passed'})
        print('PASS '+title,flush=True)
    if verify_manifest()!=count:raise RuntimeError('Manifest count changed')
    print(json.dumps({'status':'passed','manifest_files':count,'manifest_verified_before_and_after':True,
        'runs':runs,'code_sha256':{n:hashlib.sha256((ROOT/'compiler'/n).read_bytes()).hexdigest() for n in ('five_binary.py','frontend.py')},
        'companion_replayed':False,'no_external_dependencies_for_replay':True},indent=2))
if __name__=='__main__':run()
