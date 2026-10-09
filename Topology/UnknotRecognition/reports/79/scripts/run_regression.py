#!/usr/bin/env python3
"""Run the complete delivered unittest inventory in six fresh interpreters.

The output directory must not exist. All test IDs, outcomes, module hashes,
runtime source hashes and interpreter information are retained. No historical
result is overwritten. This script needs only Python's standard library;
individual tests can require the dependencies listed in repro/requirements.txt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time
import unittest


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def leaves(suite):
    for test in suite:
        if isinstance(test, unittest.TestSuite):
            yield from leaves(test)
        else:
            yield test


def worker(request, output):
    spec = json.loads(Path(request).read_text())
    # The inherited suite imports helper modules both as tests.NAME and as
    # bare NAME, matching unittest discovery with tests as the start folder.
    # Make both conventions explicit instead of depending on batch ordering.
    sys.path.insert(0, str(Path(spec['fast_source']) / 'tests'))
    sys.path.insert(0, spec['fast_source'])
    os.chdir(spec['fast_source'])
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromNames(spec['modules'])
    ids = [test.id() for test in leaves(suite)]
    started = time.perf_counter()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    record = {
        'modules': spec['modules'], 'test_ids': ids,
        'tests_loaded': len(ids), 'tests_run': result.testsRun,
        'successful': result.wasSuccessful(),
        'failures': [{'id': test.id(), 'traceback': detail}
                     for test, detail in result.failures],
        'errors': [{'id': test.id(), 'traceback': detail}
                   for test, detail in result.errors],
        'skipped': [{'id': test.id(), 'reason': reason}
                    for test, reason in result.skipped],
        'expected_failures': [test.id() for test, _ in result.expectedFailures],
        'unexpected_successes': [test.id() for test in result.unexpectedSuccesses],
        'elapsed_seconds': time.perf_counter() - started,
        'loader_errors': loader.errors,
    }
    Path(output).write_text(json.dumps(record, indent=2) + '\n')
    return 0 if result.wasSuccessful() else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parents[1]
    parser.add_argument('--fast-source', type=Path, default=root / 'repro/fast')
    parser.add_argument('--output-dir', type=Path,
                        default=root / 'reproduced/regression')
    parser.add_argument('--batches', type=int, default=6)
    parser.add_argument('--worker', nargs=2, metavar=('REQUEST', 'RESULT'))
    args = parser.parse_args()
    if args.worker:
        return worker(*args.worker)
    if args.batches < 1:
        parser.error('batches must be positive')
    fast = args.fast_source.resolve()
    paths = sorted((fast / 'tests').glob('test_*.py'))
    if not paths:
        parser.error('no test modules in ' + str(fast))
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    modules = ['tests.' + p.stem for p in paths]
    hashes = {str(p.relative_to(fast)): digest(p)
              for folder in ('fastunknot', 'tests', 'causal_research',
                             'shared_cover_research')
              for p in sorted((fast / folder).rglob('*.py'))}
    metadata = {
        'python': sys.version, 'executable': sys.executable,
        'platform': platform.platform(), 'batches': args.batches,
        'fast_source': str(fast), 'source_sha256': hashes,
        'module_inventory': [{'module': mod, 'path': str(p.relative_to(fast)),
                              'sha256': digest(p)} for mod, p in zip(modules, paths)],
    }
    (out / 'inventory.json').write_text(json.dumps(metadata, indent=2) + '\n')
    records = []
    started = time.perf_counter()
    for index in range(args.batches):
        batch = modules[index::args.batches]
        request = out / ('batch_%d_request.json' % (index + 1))
        response = out / ('batch_%d_result.json' % (index + 1))
        log = out / ('batch_%d.log' % (index + 1))
        request.write_text(json.dumps({'fast_source': str(fast), 'modules': batch}) + '\n')
        with log.open('w') as stream:
            process = subprocess.run(
                [sys.executable, '-X', 'faulthandler', str(Path(__file__).resolve()),
                 '--worker', str(request), str(response)],
                cwd=fast, stdout=stream, stderr=subprocess.STDOUT)
        record = json.loads(response.read_text()) if response.exists() else {
            'modules': batch, 'successful': False, 'tests_run': 0,
            'worker_did_not_return': True}
        record['exit_code'] = process.returncode
        record['batch'] = index + 1
        records.append(record)
        print('Batch %d/%d: %d tests, exit %d' % (
            index + 1, args.batches, record['tests_run'], process.returncode), flush=True)
    changed = [name for name, value in hashes.items()
               if not (fast / name).is_file() or digest(fast / name) != value]
    inventory_after = sorted('tests.' + p.stem for p in (fast / 'tests').glob('test_*.py'))
    summary = {
        'modules': len(modules), 'tests_run': sum(r['tests_run'] for r in records),
        'successful': all(r['successful'] and r['exit_code'] == 0 for r in records)
                      and not changed and modules == inventory_after,
        'skipped': sum(len(r.get('skipped', [])) for r in records),
        'failures': sum(len(r.get('failures', [])) for r in records),
        'errors': sum(len(r.get('errors', [])) for r in records),
        'changed_sources_during_run': changed,
        'inventory_unchanged': modules == inventory_after,
        'elapsed_seconds': time.perf_counter() - started,
        'batch_summaries': [{k: r[k] for k in ('batch', 'tests_run', 'successful',
                            'exit_code', 'elapsed_seconds') if k in r} for r in records],
    }
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    return 0 if summary['successful'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
