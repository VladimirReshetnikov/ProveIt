#!/usr/bin/env python3
"""Rebuild the packaged K215 scheduler component from .lean sources only.

Requires Python 3, a Linux/Unix host, and the complete Lean 4.32.0 distribution.
No Git checkout, network request, Lake package, or precompiled project object
is needed. The source manifest is checked before compilation.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default=shutil.which('lean') or 'lean')
    parser.add_argument('--out', type=Path, required=True,
                        help='A fresh, nonexistent build directory')
    parser.add_argument('--lock', type=Path,
                        default=Path(tempfile.gettempdir())/'proveit-proof-compiler.lock')
    parser.add_argument('--check-inputs-only', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE/'sources.json').read_text())
    for item in manifest['modules']:
        path = HERE/'sources'/item['path']
        if sha(path) != item['sha256']:
            raise SystemExit('Source hash mismatch: '+item['path'])
    if args.check_inputs_only:
        print('PASS: all '+str(len(manifest['modules']))+' source hashes match')
        return
    out = args.out.resolve()
    if out.exists():
        raise SystemExit('Refusing an existing output directory: '+str(out))
    out.mkdir(parents=True)
    (out/'logs').mkdir()
    for item in manifest['modules']:
        target = out/item['path']
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(HERE/'sources'/item['path'], target)
    env = dict(os.environ, LEAN_PATH=str(out))
    receipt = {'scope':'Concrete enumerator/scheduler component, not full ZFC endpoint',
               'status':'RUNNING', 'manifest_sha256':sha(HERE/'sources.json'),
               'source_commit':manifest['commit'], 'records':[]}
    def save():
        (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    args.lock.parent.mkdir(parents=True, exist_ok=True)
    with args.lock.open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        version = subprocess.run([args.lean,'--version'],text=True,
                                 stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        fcntl.flock(lock, fcntl.LOCK_UN)
    receipt['compiler_version'] = version.stdout.strip()
    if version.returncode or 'version 4.32.0' not in version.stdout:
        receipt['status']='UNSUPPORTED_TOOLCHAIN';save()
        raise SystemExit('This packet is pinned to Lean 4.32.0: '+version.stdout)
    save()
    for item in manifest['modules']:
        rel=Path(item['path'])
        command=[args.lean,'-o',str(rel.with_suffix('.olean')),str(rel)]
        with args.lock.open('a') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            start=time.monotonic()
            result=subprocess.run(command,cwd=out,env=env,text=True,
                                  stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            elapsed=time.monotonic()-start
            fcntl.flock(lock,fcntl.LOCK_UN)
        log=out/'logs'/(str(rel).replace('/','_')+'.log')
        log.write_text(result.stdout)
        record={'source':str(rel),'source_sha256':sha(out/rel),'command':command,
                'exit_code':result.returncode,'compiler_seconds':elapsed,
                'log':str(log.relative_to(out)),'log_sha256':sha(log)}
        if result.returncode==0:
            record['object_sha256']=sha((out/rel).with_suffix('.olean'))
        receipt['records'].append(record);save()
        print(str(rel)+': '+('PASS' if result.returncode==0 else 'FAIL'),flush=True)
        if result.returncode:
            receipt['status']='FAIL';save()
            print(result.stdout)
            raise SystemExit(result.returncode)
    receipt['status']='PASS_COMPONENT';save()

if __name__=='__main__':
    main()
