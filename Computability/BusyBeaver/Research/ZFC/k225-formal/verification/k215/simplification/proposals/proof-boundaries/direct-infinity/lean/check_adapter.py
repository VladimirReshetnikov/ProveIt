#!/usr/bin/env python3
"""Fresh serial check of the direct-Infinity adapter against a pinned checkout.

Usage: python3 check_adapter.py REPO LEAN [TARGET]
All project dependencies are compiled locally; no preexisting project olean is used.
"""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

here = Path(__file__).resolve().parent
repo = Path(sys.argv[1]).resolve()
lean = Path(sys.argv[2]).resolve()
roots = [here, repo / 'Computability/BusyBeaver/Lean',
         repo / 'Logic/FirstOrder/Lean', repo / 'SetTheory/ZF/Lean']
build = here / 'adapter-build'
logs = here / 'adapter-evidence'
build.mkdir(exist_ok=True)
logs.mkdir(exist_ok=True)
env = os.environ.copy()
env['LEAN_PATH'] = str(build)
seen, order = set(), []

def source(module):
    for root in roots:
        p = root / (module.replace('.', '/') + '.lean')
        if p.is_file():
            return p
    return None

def visit(module):
    if module in seen:
        return
    seen.add(module)
    p = source(module)
    if p is None:
        if not module.startswith(('Init', 'Lean', 'Std')):
            raise RuntimeError('Unresolved module: ' + module)
        return
    for line in p.read_text().splitlines():
        if line.startswith('import '):
            for dep in line[7:].split():
                visit(dep)
    order.append((module, p))

visit(sys.argv[3] if len(sys.argv) > 3 else 'KLowerDirectInfinityQuotient')
records = []
build_info = {
    'repository_commit': subprocess.check_output(
        ['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip(),
    'lean_version': subprocess.check_output([str(lean), '--version'], text=True).strip(),
    'target': sys.argv[3] if len(sys.argv) > 3 else 'KLowerDirectInfinityQuotient',
    'project_modules': len(order),
    'status': 'running',
    'scope': 'Actual tagged-domain and quotient Infinity; no K215 endpoint rebuild.',
}
(logs / 'build-info.json').write_text(json.dumps(build_info, indent=2) + '\n')
for module, path in order:
    output = build / (module.replace('.', '/') + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    log = logs / (module + '.log')
    print('CHECK', module, flush=True)
    with open('/tmp/proveit-k215-proof-build.lock', 'w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        started = time.monotonic()
        with log.open('w') as out:
            process = subprocess.run([str(lean), '-o', str(output), str(path)],
                                     env=env, stdout=out, stderr=subprocess.STDOUT)
    records.append(dict(module=module, source=str(path),
                        source_kind='repository' if path.is_relative_to(repo) else 'proposal',
                        source_relative=str(path.relative_to(repo if path.is_relative_to(repo) else here)),
                        sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                        log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
                        object_sha256=hashlib.sha256(output.read_bytes()).hexdigest()
                            if process.returncode == 0 else None,
                        exit=process.returncode, seconds=round(time.monotonic()-started, 3)))
    (logs / 'manifest.json').write_text(json.dumps(records, indent=2) + '\n')
    if process.returncode:
        build_info['status'] = 'failed'
        (logs / 'build-info.json').write_text(json.dumps(build_info, indent=2) + '\n')
        print(log.read_text(), flush=True)
        raise SystemExit(process.returncode)
build_info['status'] = 'passed'
(logs / 'build-info.json').write_text(json.dumps(build_info, indent=2) + '\n')
print('PASS', len(order), 'fresh modules', flush=True)
