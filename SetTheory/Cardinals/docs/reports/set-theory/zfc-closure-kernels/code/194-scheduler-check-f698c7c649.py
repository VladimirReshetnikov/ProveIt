#!/usr/bin/env python3
"""Build every bundled Lean source from scratch, recording hashes and logs.

Uses only Python's standard library and a complete Lean 4.32.0 installation.
No ProveIt checkout, Lake workspace, Mathlib, or network access is required.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True, type=Path,
                        help='Path to the Lean 4.32.0 compiler executable')
    parser.add_argument('--out', required=True, type=Path,
                        help='Fresh output directory; must not exist')
    args = parser.parse_args()
    lean = args.lean.resolve()
    out = args.out.resolve()
    src = HERE / 'src'
    manifest_bytes = (HERE / 'source_provenance.json').read_bytes()
    manifest = json.loads(manifest_bytes)
    inputs = {item['module']: item for item in manifest['modules']}
    if len(inputs) != len(manifest['modules']):
        raise RuntimeError('Duplicate module in source manifest')
    expected_paths = {item['path'] for item in inputs.values()}
    actual_paths = {p.relative_to(HERE).as_posix() for p in src.rglob('*.lean')}
    if actual_paths != expected_paths:
        raise RuntimeError('Bundled source files do not match the manifest')
    if any(src.rglob('*.olean')) or any(src.rglob('*.ilean')):
        raise RuntimeError('Source tree must contain no precompiled project objects')
    imports: dict[str, list[str]] = {}
    for module, item in inputs.items():
        source = HERE / item['path']
        data = source.read_bytes()
        if sha(data) != item['source_sha256']:
            raise RuntimeError('Source hash mismatch: ' + module)
        imports[module] = re.findall(
            r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)', data.decode(), re.M)
        for dep in imports[module]:
            if dep not in inputs and dep.split('.')[0] not in {'Init', 'Std', 'Lean'}:
                raise RuntimeError('Unbundled nonstandard import: ' + dep)
    order: list[str] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        if module in visiting:
            raise RuntimeError('Cyclic project imports at: ' + module)
        visiting.add(module)
        for dep in imports[module]:
            if dep in inputs:
                visit(dep)
        visiting.remove(module)
        visited.add(module)
        order.append(module)

    for module in sorted(inputs):
        visit(module)
    version_run = subprocess.run([str(lean), '--version'], capture_output=True,
                                 text=True, check=True)
    version = version_run.stdout.strip()
    if 'version 4.32.0,' not in version:
        raise RuntimeError('Expected Lean 4.32.0: ' + version)
    if out.exists():
        raise RuntimeError('A new output directory is required: ' + str(out))
    out.mkdir(parents=True)
    objects = out / 'objects'
    logs = out / 'logs'
    objects.mkdir()
    logs.mkdir()
    env = dict(os.environ)
    # The compiler's own standard library is still supplied by its installation.
    # No previously built project objects are included in this search path.
    env['LEAN_PATH'] = str(objects)
    receipt = {
        'schema_version': 1,
        'base_commit': manifest['base_commit'],
        'scope': manifest['scope'],
        'lean_version': version,
        'compiler_binary_sha256': sha(lean.read_bytes()),
        'checker_sha256': sha(Path(__file__).read_bytes()),
        'source_provenance_sha256': sha(manifest_bytes),
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'project_objects_reused': False,
        'project_search_path': ['OUTPUT/objects'],
        'module_count_expected': len(order),
        'build_order': order,
        'status': 'running',
        'modules': [],
    }

    def save() -> None:
        (out / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')

    save()
    build_started = time.monotonic()
    for module in order:
        item = inputs[module]
        rel = Path(module.replace('.', '/') + '.lean')
        obj_rel = Path('objects') / rel.with_suffix('.olean')
        obj = out / obj_rel
        obj.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), '-j1', '-M8192', '-o', str(obj), str(rel)]
        started = time.monotonic()
        run = subprocess.run(command, cwd=src, env=env, capture_output=True, text=True)
        elapsed = time.monotonic() - started
        output = run.stdout + run.stderr
        log_rel = Path('logs') / (module + '.log')
        (out / log_rel).write_text(output)
        record = {
            'module': module,
            'source': item['path'],
            'source_sha256': item['source_sha256'],
            'direct_imports': imports[module],
            'command': ['LEAN', '-j1', '-M8192', '-o',
                        'OUTPUT/' + obj_rel.as_posix(), rel.as_posix()],
            'exit_code': run.returncode,
            'seconds': elapsed,
            'log': log_rel.as_posix(),
            'log_sha256': sha(output.encode()),
            'warning_count': len(re.findall(r'\bwarning:', output)),
            'axiom_reports': [line for line in output.splitlines()
                              if 'axioms' in line or line.startswith('[')],
        }
        if obj.exists():
            record['olean_sha256'] = sha(obj.read_bytes())
        receipt['modules'].append(record)
        failed = (run.returncode != 0 or not obj.exists()
                  or 'sorryAx' in output or "uses 'sorry'" in output
                  or re.search(r'\berror:', output) is not None)
        print(module, 'exit', run.returncode, f'{elapsed:.3f}s', flush=True)
        if failed:
            receipt['status'] = 'failed'
            receipt['failed_module'] = module
            save()
            print(output)
            raise SystemExit(run.returncode or 1)
        save()
    receipt['status'] = 'passed'
    receipt['module_count_completed'] = len(receipt['modules'])
    receipt['compiler_seconds_total'] = sum(r['seconds'] for r in receipt['modules'])
    receipt['elapsed_seconds'] = time.monotonic() - build_started
    receipt['warning_count'] = sum(r['warning_count'] for r in receipt['modules'])
    receipt['completed_utc'] = datetime.now(timezone.utc).isoformat()
    save()
    print('PASS:', len(order), 'fresh Lean modules;', receipt['warning_count'],
          'warnings;', f"{receipt['compiler_seconds_total']:.3f}s compiler time")


if __name__ == '__main__':
    main()
