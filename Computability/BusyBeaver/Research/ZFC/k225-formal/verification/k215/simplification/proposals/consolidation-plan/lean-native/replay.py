#!/usr/bin/env python3
"""Build the native Replacement overlay and its clients from fresh Lean objects.

Scope: generic KEndpoint and legacy Replacement compatibility, not the physical
K215 source/boot/site certificate closure. No network or repository writes.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
import tomllib

PIN = 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6'
HERE = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--build', type=Path, required=True)
    args = parser.parse_args()
    repo, lean, build = args.repo.resolve(), args.lean.resolve(), args.build.resolve()
    pin = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    if pin != PIN:
        raise SystemExit(f'Expected {PIN}, got {pin}')
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    if 'version 4.32.0,' not in version:
        raise SystemExit(f'Expected Lean 4.32.0, got {version}')
    if build.exists():
        raise SystemExit('Use a fresh build directory')
    build.mkdir(parents=True)
    roots = list(dict.fromkeys(repo / lib.get('srcDir', '.')
        for lib in tomllib.loads((repo / 'lakefile.toml').read_text())['lean_lib']))
    overlays = {'.'.join(p.relative_to(HERE / 'overlay').with_suffix('').parts): p
        for p in (HERE / 'overlay').rglob('*.lean')}
    audits = {p.stem: p for p in (HERE / 'audits').glob('*.lean')}
    overlays.update(audits)
    sources, imports, order, active = {}, {}, [], set()
    def visit(name):
        if name in active:
            raise RuntimeError(f'Import cycle: {name}')
        if name in sources or name.split('.')[0] in ('Init', 'Std', 'Lean'):
            return
        if name in overlays:
            source = overlays[name]
        else:
            relative = Path(*name.split('.')).with_suffix('.lean')
            paths = [p / relative for p in roots if (p / relative).is_file()]
            if len(paths) != 1:
                raise RuntimeError(f'Expected one source for {name}: {paths}')
            source = paths[0]
        deps = []
        for line in source.read_text().splitlines():
            match = re.match(r'^(?:public\s+)?import\s+(.+)', line)
            if match:
                deps.extend(match.group(1).split('--', 1)[0].split())
        active.add(name)
        for dep in deps:
            visit(dep)
        active.remove(name)
        sources[name], imports[name] = source, deps
        order.append(name)
    for name in ['AuditNativeEndpoint', 'AuditLegacyReplacement']:
        visit(name)
    out, logs, snaps = build / 'objects', build / 'logs', build / 'sources'
    for d in (out, logs, snaps):
        d.mkdir()
    receipt = {'status': 'RUNNING', 'repository_commit': pin, 'toolchain': version,
        'scope': __doc__, 'records': []}
    (build / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    env = dict(os.environ, LEAN_PATH=str(out))
    with open('/tmp/k215-simplification-proof.lock', 'w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for i, name in enumerate(order):
            src = sources[name]
            obj = out / (name.replace('.', '/') + '.olean')
            obj.parent.mkdir(parents=True, exist_ok=True)
            snapshot = snaps / (name.replace('.', '/') + '.lean')
            snapshot.parent.mkdir(parents=True, exist_ok=True)
            snapshot.write_bytes(src.read_bytes())
            command = [str(lean), '-o', str(obj), str(src)]
            print(f'{i + 1}/{len(order)} {name}', flush=True)
            start = time.monotonic()
            completed = subprocess.run(command, text=True, capture_output=True, env=env)
            logfile = logs / (name + '.log')
            logfile.write_text(completed.stdout + completed.stderr)
            receipt['records'].append({'module': name,
                'source': ('packet:' + str(src.relative_to(HERE))) if src.is_relative_to(HERE)
                    else ('repo:' + str(src.relative_to(repo))),
                'source_sha256': sha(src), 'imports': imports[name],
                'source_bytes': src.stat().st_size, 'source_lines': len(src.read_text().splitlines()),
                'command': command, 'exit_code': completed.returncode,
                'elapsed_seconds': round(time.monotonic() - start, 6),
                'log': str(logfile.relative_to(build)), 'log_sha256': sha(logfile),
                'object_sha256': sha(obj) if obj.exists() else None})
            if completed.returncode or 'sorryAx' in logfile.read_text():
                receipt['status'] = 'FAIL'
                (build / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
                print(logfile.read_text(), flush=True)
                return 1
            (build / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    receipt['status'] = 'PASS'
    receipt['project_modules'] = len(order) - len(audits)
    receipt['audit_modules'] = len(audits)
    (build / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('PASS', flush=True)
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
