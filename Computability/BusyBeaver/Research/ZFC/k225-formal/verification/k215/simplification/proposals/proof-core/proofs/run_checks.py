#!/usr/bin/env python3
"""Freshly compile the pinned local proof closure; no cached oleans are used."""
from __future__ import annotations
import argparse, hashlib, json, os, pathlib, re, shutil, subprocess, tempfile, time

HERE = pathlib.Path(__file__).resolve().parent

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lean', required=True, help='Lean 4.32.0 compiler executable')
    ap.add_argument('--build-dir', type=pathlib.Path)
    ap.add_argument('--roots', nargs='+', default=['DomRho8PublicAudit', 'PrintKSim', 'BusyBeaver.ZFC.SubtermImplication'])
    args = ap.parse_args()
    sources = HERE / 'formal'
    build = args.build_dir or pathlib.Path(tempfile.mkdtemp(prefix='k215-proof-check-'))
    if build.exists() and any(build.iterdir()):
        raise SystemExit('Build directory must be empty; fresh object verification is required.')
    build.mkdir(parents=True, exist_ok=True)
    ordered, visiting, done = [], set(), set()
    def visit(name):
        if name in done: return
        if name in visiting: raise RuntimeError('Import cycle: ' + name)
        file = sources / (name.replace('.', '/') + '.lean')
        if not file.exists():
            if name == 'Init' or name.startswith(('Init.', 'Lean.', 'Std.')): return
            raise FileNotFoundError(file)
        visiting.add(name)
        for line in file.read_text().splitlines():
            if line.startswith('import '):
                for dependency in line[len('import '):].split(): visit(dependency)
        visiting.remove(name); done.add(name); ordered.append(name)
    for root in args.roots: visit(root)
    for name in ordered:
        relative = name.replace('.', '/') + '.lean'
        target = build / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(sources / relative, target)
    compiler = pathlib.Path(args.lean).resolve()
    env = os.environ.copy(); env['LEAN_PATH'] = str(build)
    version = subprocess.run([str(compiler), '--version'], capture_output=True, text=True, check=True).stdout.strip()
    if 'version 4.32.0' not in version: raise SystemExit('Expected Lean 4.32.0: ' + version)
    report = {'base_commit':'aa66d0a33f1f8237a348899eb8095b045a502832', 'compiler':version,
              'roots':args.roots,'fresh_modules':len(ordered),'records':[],'status':'RUNNING'}
    for name in ordered:
        relative = name.replace('.', '/')
        started = time.monotonic()
        result = subprocess.run([str(compiler), '-o', relative+'.olean', relative+'.lean'],
                                cwd=build, env=env, capture_output=True, text=True)
        record = {'module':name, 'source_sha256':digest(build/(relative+'.lean')),
                  'seconds':time.monotonic()-started, 'exit_code':result.returncode,
                  'stdout':result.stdout,'stderr':result.stderr}
        if result.returncode == 0: record['olean_sha256']=digest(build/(relative+'.olean'))
        report['records'].append(record)
        print(name, result.returncode, flush=True)
        if result.returncode:
            report['status']='FAIL'; (build/'receipt.json').write_text(json.dumps(report,indent=2))
            raise SystemExit(result.stdout+result.stderr)
    report['status']='PASS'
    (build/'receipt.json').write_text(json.dumps(report,indent=2))
    print(json.dumps({'status':'PASS','fresh_modules':len(ordered),'receipt':str(build/'receipt.json')}))

if __name__ == '__main__': main()
