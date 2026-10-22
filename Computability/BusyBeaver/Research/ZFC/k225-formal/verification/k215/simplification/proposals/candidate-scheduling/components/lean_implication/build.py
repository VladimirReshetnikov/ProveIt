#!/usr/bin/env python3
"""Fresh, serial component build; no precompiled project objects are reused."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

BASE = '57541fe0cfe3af62b4cb58747d8d1d7c16b338d5'
HERE = Path(__file__).resolve().parent
OVERLAY = HERE / 'overlay'
ROOTS = {
    'BusyBeaver': Path('Computability/BusyBeaver/Lean'),
    'FirstOrder': Path('Logic/FirstOrder/Lean'),
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    repo, lean, out = args.repo.resolve(), args.lean.resolve(), args.out.resolve()
    rev = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=repo, capture_output=True,
                         text=True, check=True).stdout.strip()
    if rev != BASE:
        raise RuntimeError('Reconcile the patch before building another revision: ' + rev)
    version = subprocess.run([str(lean), '--version'], capture_output=True,
                             text=True, check=True).stdout.strip()
    if 'version 4.32.0,' not in version:
        raise RuntimeError('Expected Lean 4.32.0: ' + version)
    if out.exists():
        raise RuntimeError('Fresh output directory required: ' + str(out))
    src, objects, logs = out / 'src', out / 'objects', out / 'logs'
    src.mkdir(parents=True); objects.mkdir(); logs.mkdir()
    order, inputs, imports = [], {}, {}

    def visit(module):
        if module in inputs:
            return
        if module == 'SharedBasisAudit':
            origin = HERE / 'SharedBasisAudit.lean'
            rel = None
        else:
            prefix = module.split('.')[0]
            if prefix not in ROOTS:
                return
            rel = ROOTS[prefix] / (module.replace('.', '/') + '.lean')
            origin = OVERLAY / rel
            if not origin.exists():
                origin = repo / rel
        data = origin.read_bytes()
        inputs[module] = {'origin': str(origin), 'repo_path': str(rel) if rel else None,
                          'source_sha256': sha(data), 'overlay': origin.is_relative_to(OVERLAY)}
        target = src / (module.replace('.', '/') + '.lean')
        target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(data)
        deps = re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)', data.decode(), re.M)
        imports[module] = deps
        for dep in deps:
            visit(dep)
        order.append(module)

    visit('SharedBasisAudit')
    env = dict(os.environ)
    env['LEAN_PATH'] = str(objects)
    receipt = {'base_commit': BASE, 'lean_version': version, 'scope':
               'Fresh shared-basis component closure plus typed compatibility audit; no KEndpoint215 build.',
               'modules': []}
    for module in order:
        rel = Path(module.replace('.', '/') + '.lean')
        obj = objects / rel.with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), '-j1', '-M8192', '-o', str(obj), str(rel)]
        started = time.monotonic()
        run = subprocess.run(command, cwd=src, env=env, capture_output=True, text=True)
        elapsed = time.monotonic() - started
        text = run.stdout + run.stderr
        log = logs / (module + '.log'); log.write_text(text)
        record = dict(inputs[module], module=module, direct_imports=imports[module],
                      command=command, exit_code=run.returncode, seconds=elapsed,
                      log_sha256=sha(text.encode()), log=str(log.relative_to(out)))
        if obj.exists():
            record['olean_sha256'] = sha(obj.read_bytes())
        receipt['modules'].append(record)
        (out / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
        print(module, 'exit', run.returncode, f'{elapsed:.3f}s', flush=True)
        if run.returncode or 'sorryAx' in text or re.search(r'\berror:', text):
            print(text)
            raise SystemExit(run.returncode or 1)
    print((logs / 'SharedBasisAudit.log').read_text())

if __name__ == '__main__':
    main()
