#!/usr/bin/env python3
"""Verify the zero-spare MP-first215 machine and the separate rejected-source audit.
Default checks exact construction, startup, stored census, and bounded novelty.
--runtime freshly rederives all 6209 arbitrary-natural primitive cases.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile

ROOT=Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory():
    manifest=json.loads((ROOT/'manifest.json').read_text())
    expected=manifest['files']
    actual={}
    for path in ROOT.rglob('*'):
        if path.is_symlink():
            raise RuntimeError('Symlinks are not permitted in the verified packet: '+str(path.relative_to(ROOT)))
        if not path.is_file() or '__pycache__' in path.relative_to(ROOT).parts:
            continue
        name=path.relative_to(ROOT).as_posix()
        if name!='manifest.json':
            actual[name]=digest(path)
    if actual!=expected:
        missing=sorted(set(expected)-set(actual))
        extra=sorted(set(actual)-set(expected))
        changed=sorted(name for name in expected.keys()&actual.keys() if expected[name]!=actual[name])
        raise RuntimeError('Manifest mismatch: '+json.dumps(dict(missing=missing,extra=extra,changed=changed)))
    return digest(ROOT/'manifest.json')

def run(script,args,work,logname):
    log=work/logname
    with log.open('w') as stream:
        process=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=work,stdout=stream,stderr=subprocess.STDOUT)
    if process.returncode:
        print(log.read_text()[-8000:],file=sys.stderr)
        raise RuntimeError(f'{logname}: verifier exited with status {process.returncode}')
    print('PASS '+logname,flush=True)
    return dict(exit_code=0,log=logname,log_sha256=digest(log))

def main():
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Run with Python assertions enabled, without -O or -OO.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runtime',action='store_true',help='Freshly rederive all 6209 arbitrary-natural runtime cases')
    parser.add_argument('--work',type=Path,help='New output directory outside the packet')
    args=parser.parse_args()
    before=inventory()
    temp=None
    if args.work:
        work=args.work.resolve()
        if work==ROOT or ROOT in work.parents:
            raise RuntimeError('Output must be outside the packet.')
        work.mkdir(parents=True,exist_ok=False)
    else:
        temp=tempfile.TemporaryDirectory(prefix='k215-zero-mp-first-')
        work=Path(temp.name)
    command=['--out',work/'machine']+(['--runtime'] if args.runtime else [])
    machine=run(ROOT/'machine/verify.py',command,work,'machine.log')
    machine['verification']=json.loads((work/'machine/verification.json').read_text())
    rejection=run(ROOT/'research/rejected_biased/verify.py',[],work,'rejected_biased.log')
    if inventory()!=before:
        raise RuntimeError('Input packet changed during verification.')
    result=dict(status='ALL_REQUESTED_CHECKS_PASS',states=215,rows=430,
        manifest_sha256=before,fresh_runtime=args.runtime,machine=machine,
        rejected_source_audit=rejection,
        scope='One materially distinct 215-state blank-start construction. No 214-state result or new exact-byte proof-assistant endpoint.')
    (work/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
    if temp:temp.cleanup()
    else:print('Retained receipts:',work)

if __name__=='__main__':main()
