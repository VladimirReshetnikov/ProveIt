#!/usr/bin/env python3
"""Compile and recursively kernel-check the standalone Rocq core from a clean tree.
The Coq environment (if a relocatable distribution requires one) is inherited.
No compiler or library binaries are included in this research packet.
"""
from __future__ import annotations
import argparse, hashlib, json, pathlib, shutil, subprocess, tempfile, time
HERE = pathlib.Path(__file__).resolve().parent

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--coqc', default='coqc')
    ap.add_argument('--coqchk', default='coqchk')
    ap.add_argument('--build-dir', type=pathlib.Path)
    ap.add_argument('--module', choices=['DominatedImplication', 'FourShapeImplication'], default='DominatedImplication')
    args = ap.parse_args()
    build = args.build_dir or pathlib.Path(tempfile.mkdtemp(prefix='k215-rocq-core-'))
    if build.exists() and any(build.iterdir()):
        raise SystemExit('Build directory must be empty; fresh object verification is required.')
    build.mkdir(parents=True, exist_ok=True)
    source = HERE / ('rocq/' + args.module + '.v')
    shutil.copyfile(source, build/source.name)
    version = subprocess.run([args.coqc, '-v'], capture_output=True, text=True, check=True)
    report = {'base_commit':'aa66d0a33f1f8237a348899eb8095b045a502832',
              'source_module':args.module,
              'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
              'compiler':version.stdout.strip(), 'status':'RUNNING', 'records':[]}
    commands = [[args.coqc, source.name], [args.coqchk, args.module]]
    for command in commands:
        start = time.monotonic()
        result = subprocess.run(command, cwd=build, capture_output=True, text=True)
        record = {'tool':pathlib.Path(command[0]).name, 'arguments':command[1:],
                  'seconds':time.monotonic()-start, 'exit_code':result.returncode,
                  'stdout':result.stdout,'stderr':result.stderr}
        report['records'].append(record)
        print(record['tool'], result.returncode, flush=True)
        if result.returncode:
            report['status']='FAIL'; (build/'receipt.json').write_text(json.dumps(report,indent=2))
            raise SystemExit(result.stdout+result.stderr)
    report['vo_sha256'] = hashlib.sha256((build/(args.module+'.vo')).read_bytes()).hexdigest()
    report['status']='PASS'
    (build/'receipt.json').write_text(json.dumps(report,indent=2))
    print(json.dumps({'status':'PASS','receipt':str(build/'receipt.json')}))

if __name__ == '__main__': main()
