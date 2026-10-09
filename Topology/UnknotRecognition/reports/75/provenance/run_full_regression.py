"""Run every maintained/incoming/new test module in six fresh processes.

The first monolithic run ended without a unittest summary. This runner records
an exact module inventory and uses fresh interpreter batches to avoid relying
on an accumulated interpreter state. No test/runtime source is rewritten.
"""

import argparse
from datetime import datetime, timezone
import faulthandler
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
import unittest


ROOT = Path(__file__).resolve().parents[1]
FAST = ROOT/'work/fast'
PROVENANCE = ROOT/'provenance'


def now():
    return datetime.now(timezone.utc).isoformat()


def sources():
    paths = sorted((FAST/'tests').glob('test*.py'))
    return [dict(module=path.stem, path=str(path.relative_to(FAST)),
                 sha256=sha256(path.read_bytes()).hexdigest()) for path in paths]


def child(number):
    manifest = json.loads((PROVENANCE/'full_tests_inventory.json').read_text())
    modules = manifest['batches'][number]['modules']
    sys.path.insert(0, str(FAST))
    sys.path.insert(0, str(FAST/'tests'))
    faulthandler.enable()
    faulthandler.dump_traceback_later(120, repeat=True)
    started, clock = now(), time.perf_counter()
    progress_path = PROVENANCE/f'full_tests_batch_{number+1}_progress.json'

    class RecordingResult(unittest.TextTestResult):
        def stopTest(self, test):
            super().stopTest(test)
            progress = dict(batch=number+1, last_test=test.id(), tests_run=self.testsRun,
                            failures=len(self.failures), errors=len(self.errors),
                            skipped=len(self.skipped), elapsed_seconds=time.perf_counter()-clock,
                            ru_maxrss_native_units=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                            updated_utc=now())
            progress_path.write_text(json.dumps(progress, indent=2)+'\n')

    suite = unittest.defaultTestLoader.loadTestsFromNames(modules)
    def identities(tests):
        for test in tests:
            if isinstance(test, unittest.TestSuite):
                yield from identities(test)
            else:
                yield test.id()
    loaded_ids = list(identities(suite))
    result = unittest.TextTestRunner(verbosity=2, resultclass=RecordingResult).run(suite)
    faulthandler.cancel_dump_traceback_later()
    summary = dict(batch=number+1, modules=modules, test_ids=loaded_ids,
                   tests_loaded=len(loaded_ids), tests_run=result.testsRun,
                   successes=result.testsRun-len(result.errors)-len(result.failures)
                             -len(result.skipped)-len(result.expectedFailures)
                             -len(result.unexpectedSuccesses),
                   skipped=len(result.skipped), expected_failures=len(result.expectedFailures),
                   unexpected_successes=len(result.unexpectedSuccesses),
                   failures=[dict(test=test.id(), traceback=trace) for test, trace in result.failures],
                   errors=[dict(test=test.id(), traceback=trace) for test, trace in result.errors],
                   started_utc=started, finished_utc=now(),
                   elapsed_seconds=time.perf_counter()-clock,
                   ru_maxrss_native_units=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                   status='PASSED' if result.wasSuccessful() else 'FAILED')
    (PROVENANCE/f'full_tests_batch_{number+1}.json').write_text(
        json.dumps(summary, indent=2)+'\n')
    return 0 if result.wasSuccessful() else 1


def parent():
    inventory = sources()
    modules = [item['module'] for item in inventory]
    batches = [dict(batch=i+1, modules=modules[i::6]) for i in range(6)]
    manifest = dict(python=sys.executable, python_version=sys.version,
                    working_directory=str(FAST), module_inventory=inventory,
                    total_modules=len(modules), batches=batches,
                    partition='sorted module names distributed round-robin among six batches')
    (PROVENANCE/'full_tests_inventory.json').write_text(json.dumps(manifest, indent=2)+'\n')
    result = dict(status='RUNNING', strategy='six fresh interpreter batches',
                  started_utc=now(), exact_module_inventory=str(PROVENANCE/'full_tests_inventory.json'),
                  total_modules=len(modules), batches=[], tests_run=0,
                  first_monolithic_attempt=str(PROVENANCE/'full_tests_initial.json'),
                  companion_sources=str(PROVENANCE/'companion_sources.json'))
    clock = time.perf_counter()
    env = dict(os.environ)
    env['PYTHONPATH'] = str(FAST/'tests')+os.pathsep+env.get('PYTHONPATH', '')
    combined_path = PROVENANCE/'full_tests.log'
    with combined_path.open('w') as combined:
        combined.write('Complete module inventory partitioned into six fresh Python processes.\n')
        combined.flush()
        for i in range(6):
            log_path = PROVENANCE/f'full_tests_batch_{i+1}.log'
            command = [sys.executable, '-X', 'faulthandler', str(Path(__file__).resolve()),
                       '--batch', str(i)]
            print('Starting regression batch', i+1, 'of 6, modules', len(batches[i]['modules']),
                  now(), flush=True)
            with log_path.open('w') as log:
                process = subprocess.run(command, cwd=FAST, env=env, stdout=log,
                                         stderr=subprocess.STDOUT)
            summary_path = PROVENANCE/f'full_tests_batch_{i+1}.json'
            if summary_path.exists():
                summary = json.loads(summary_path.read_text())
            else:
                summary = dict(batch=i+1, modules=batches[i]['modules'],
                               status='ABRUPT_EXIT', tests_run=None)
            summary.update(exit_code=process.returncode, command=command,
                           log_path=str(log_path))
            summary_path.write_text(json.dumps(summary, indent=2)+'\n')
            result['batches'].append(summary)
            result['tests_run'] += summary['tests_run'] or 0
            result['elapsed_seconds'] = time.perf_counter()-clock
            combined.write(f'\n=== BATCH {i+1} ===\n')
            combined.write(log_path.read_text(errors='replace'))
            combined.flush()
            (PROVENANCE/'full_tests.json').write_text(json.dumps(result, indent=2)+'\n')
            print('Completed batch', i+1, summary['status'], 'tests', summary['tests_run'],
                  'exit', process.returncode, flush=True)
    visited = [m for batch in result['batches'] for m in batch['modules']]
    result.update(finished_utc=now(), elapsed_seconds=time.perf_counter()-clock,
                  zero_module_omissions=sorted(visited) == sorted(modules)
                                        and len(visited) == len(set(visited)),
                  test_source_hashes_unchanged=sources() == inventory)
    result['status'] = ('PASSED' if all(batch['status'] == 'PASSED'
                                      and batch['exit_code'] == 0 for batch in result['batches'])
                         and result['zero_module_omissions']
                         and result['test_source_hashes_unchanged'] else 'FAILED')
    result['failures'] = sum(len(batch.get('failures', [])) for batch in result['batches'])
    result['errors'] = sum(len(batch.get('errors', [])) for batch in result['batches'])
    result['skipped'] = sum(batch.get('skipped', 0) for batch in result['batches'])
    result['tests_loaded'] = sum(batch.get('tests_loaded', 0) for batch in result['batches'])
    (PROVENANCE/'full_tests.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'batches'}, indent=2),
          flush=True)
    return 0 if result['status'] == 'PASSED' else 1


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batch', type=int)
    args = parser.parse_args()
    sys.exit(parent() if args.batch is None else child(args.batch))
