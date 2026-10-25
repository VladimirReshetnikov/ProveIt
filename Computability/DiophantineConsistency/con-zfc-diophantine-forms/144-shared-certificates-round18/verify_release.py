#!/usr/bin/env python3
"""Verify release identities and execute the explicit portable verification plan."""
import argparse, hashlib, json, os, pathlib, subprocess, sys, time
ROOT = pathlib.Path(__file__).resolve().parent
os.environ['PYTHONDONTWRITEBYTECODE']='1'

def verify():
    manifest = json.loads((ROOT / 'MANIFEST_SHA256.json').read_text())
    for name, expected in manifest['files'].items():
        path = ROOT / name
        if not path.is_file() or path.is_symlink():
            raise ValueError('Missing or nonregular release file: ' + name)
        data = path.read_bytes()
        if len(data) != expected['bytes'] or hashlib.sha256(data).hexdigest() != expected['sha256']:
            raise ValueError('Release identity mismatch: ' + name)
    prior=ROOT/'prior_direct_closure'
    old=json.loads((prior/'MANIFEST_SHA256.json').read_text())['files']
    retained=0
    for path in prior.rglob('*'):
        if not path.is_file() or path.name=='MANIFEST_SHA256.json':
            continue
        name=path.relative_to(prior).as_posix()
        data=path.read_bytes(); expected=old[name]
        if len(data)!=expected['bytes'] or hashlib.sha256(data).hexdigest()!=expected['sha256']:
            raise ValueError('Inherited source identity mismatch: '+name)
        retained+=1
    plan = json.loads((ROOT / 'VERIFY_PLAN.json').read_text())
    runs=[]
    for step in plan['steps']:
        command=[sys.executable, '-B'] + step['arguments']
        start=time.monotonic()
        result=subprocess.run(command,cwd=ROOT / step.get('cwd','.'),capture_output=True,text=True)
        runs.append({'name':step['name'],'arguments':step['arguments'],
                     'returncode':result.returncode,'seconds':round(time.monotonic()-start,3),
                     'stdout':result.stdout,'stderr':result.stderr})
        if result.returncode:
            print(json.dumps({'status':'FAIL','manifest_files':len(manifest['files']),'runs':runs},indent=2))
            raise RuntimeError('Failed verification: '+step['name'])
    return {'status':'PASS','manifest_files':len(manifest['files']),'authenticated_prior_files':retained,'commands':len(runs),'runs':runs,
            'boundary':'Finite identities, source bindings and reconstruction, not a consistency decision or new formal kernel certificate.'}

if __name__ == '__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=pathlib.Path);args=parser.parse_args()
    report=verify();text=json.dumps(report,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text)
