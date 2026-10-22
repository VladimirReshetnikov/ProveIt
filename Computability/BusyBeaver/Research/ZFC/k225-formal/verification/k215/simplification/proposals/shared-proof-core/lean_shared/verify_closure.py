#!/usr/bin/env python3
"""Rebuild the changed core, exact basis API and unchanged immediate clients.

Pass a pinned ProveIt checkout and a Lean 4.32.0 compiler.  Source copies and
outputs are isolated; the repository is never modified.  This is a proof
dependency build, not the complete machine endpoint rebuild.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
EXPECTED_HEAD = '2ca3a5c16f0876d2cab842056353c03a1ed2f5f0'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--lean', default='lean')
    args = parser.parse_args()
    repo = args.repo.resolve()
    head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    if head != EXPECTED_HEAD:
        raise SystemExit(f'Expected source commit {EXPECTED_HEAD}, got {head}')
    roots = {'BusyBeaver': repo / 'Computability/BusyBeaver/Lean',
             'FirstOrder': repo / 'Logic/FirstOrder/Lean'}
    seen = {}
    order = []
    def visit(module):
        if module in seen:
            return
        relative = Path(module.replace('.', '/') + '.lean')
        source = HERE / relative
        if not source.is_file():
            source = roots[module.split('.')[0]] / relative
            pinned = subprocess.check_output(
                ['git', '-C', str(repo), 'show', f'{head}:{source.relative_to(repo)}'])
            if source.read_bytes() != pinned:
                raise SystemExit(f'Working source differs from pinned commit: {source}')
        seen[module] = source
        for line in source.read_text().splitlines():
            if line.startswith('import '):
                for dependency in line[7:].split():
                    if dependency.split('.')[0] in roots:
                        visit(dependency)
        order.append((module, relative, source))
    for module in ['BusyBeaver.ZFC.DominatedImplication',
                   'BusyBeaver.ZFC.ImplicationalBasis',
                   'BusyBeaver.ZFC.Lukasiewicz', 'BusyBeaver.ZFC.KCodeDom',
                   'BasisPublicAudit', 'DownstreamPublicAudit']:
        visit(module)
    build = HERE / 'build'
    logs = HERE / 'verification' / 'logs'
    build.mkdir(exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(build))
    records = []
    version = subprocess.check_output([args.lean, '--version'], text=True).strip()
    if 'version 4.32.0' not in version:
        raise SystemExit(f'Unexpected Lean version: {version}')
    for index, (module, relative, source) in enumerate(order):
        target = build / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        output = target.with_suffix('.olean')
        output.unlink(missing_ok=True)
        command = [args.lean, '-o', str(relative.with_suffix('.olean')), str(relative)]
        start = time.monotonic()
        result = subprocess.run(command, cwd=build, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - start
        log = logs / f'{index:02}-{module}.log'
        log.write_text(result.stdout)
        record = {'module': module, 'source': str(source.relative_to(repo)) if source.is_relative_to(repo) else str(source.relative_to(HERE)),
                  'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                  'exit_code': result.returncode, 'elapsed_seconds': elapsed,
                  'log': str(log.relative_to(HERE))}
        records.append(record)
        print(f'{module}: exit={result.returncode} time={elapsed:.3f}s', flush=True)
        (HERE / 'verification' / 'closure.json').write_text(json.dumps(
            {'source_commit': head, 'lean_version': version, 'records': records,
             'complete': len(records) == len(order) and all(r['exit_code'] == 0 for r in records)}, indent=2) + '\n')
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)

if __name__ == '__main__':
    main()
