"""Read-only verification of the delivered research package."""
from pathlib import Path
import concurrent.futures
import gzip
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True


def run_case(job):
    checker, optimized, case = job
    process = subprocess.run([sys.executable, *(['-O'] if optimized else []), str(checker)],
                             input=json.dumps(case['packet']), text=True,
                             capture_output=True, timeout=30)
    accepted = process.returncode == 0 and process.stdout == 'ACCEPT\n'
    rejected = process.returncode != 0 and process.stdout == 'REJECT\n'
    return {'checker': checker.name, 'optimized': optimized, 'case': case['name'],
            'passed': accepted == case['accept'] and (accepted or rejected)}


def main():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for item in manifest['files']:
        data = (ROOT / item['path']).read_bytes()
        if len(data) != item['bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
            raise SystemExit('Manifest mismatch: ' + item['path'])
    spec = importlib.util.spec_from_file_location('measure', ROOT / 'tools/measure.py')
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    expected = json.loads((ROOT / 'evidence/current_metrics.json').read_text())
    fields = ('source_tokens', 'normalized_tokens', 'ast_nodes', 'normalized_bytes',
              'raw_bytes', 'sha256', 'gzip9_raw_bytes', 'gzip9_normalized_bytes')
    for item in expected['programs']:
        actual = measure.measure(ROOT / item['file'])
        for key in fields:
            if actual[key] != item[key]:
                raise SystemExit(f'Metric mismatch: {item["file"]}: {key}')
        compressed = (ROOT / item['file']).with_suffix('.py.gz')
        if compressed.exists():
            if gzip.decompress(compressed.read_bytes()) != (ROOT / item['file']).read_bytes():
                raise SystemExit('Gzip contents mismatch: ' + item['file'])
            if compressed.stat().st_size != item['gzip9_raw_bytes']:
                raise SystemExit('Gzip size mismatch: ' + item['file'])
    comparison = subprocess.run([sys.executable, '-B', str(ROOT / 'reference/audit/reproduce_comparators.py')],
                                cwd=ROOT, text=True, capture_output=True, timeout=30)
    if comparison.returncode:
        raise SystemExit(comparison.stdout + comparison.stderr)
    cases = json.loads((ROOT / 'tests/cases.json').read_text())['cases']
    checkers = [ROOT / 'code' / name for name in
                ('checker_loop.py', 'checker_bytes.py', 'readable_checker.py')]
    jobs = [(checker, opt, case) for checker in checkers
            for opt in (False, True) for case in cases]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        runs = list(pool.map(run_case, jobs))
    if not all(r['passed'] for r in runs):
        raise SystemExit(json.dumps([r for r in runs if not r['passed']], indent=2))
    with tempfile.TemporaryDirectory(prefix='ipra-reproduction-') as tmp:
        receipt = Path(tmp) / 'regressions.json'
        regression = subprocess.run([
            sys.executable, str(ROOT / 'tools/run_new_tests.py'),
            '--loop', str(checkers[0]), '--bytes', str(checkers[1]),
            '--readable', str(checkers[2]),
            '--baseline', str(ROOT / 'reference/audit/comparators/flat_computation.py'),
            '--cases', str(ROOT / 'tests/cases.json'), '--output', str(receipt)],
            text=True, capture_output=True, timeout=60)
        if regression.returncode:
            raise SystemExit(regression.stdout + regression.stderr)
        detail = json.loads(receipt.read_text())
    print(json.dumps({'manifest_files': len(manifest['files']),
                      'complete_candidate_programs': len(checkers),
                      'inherited_cases': len(cases),
                      'inherited_case_runs': len(runs),
                      'targeted_regression_runs': detail['new_regression_runs'],
                      'all_passed': True,
                      'scope': 'Finite execution and reproducibility; not a formal metatheorem proof'},
                     indent=2))


if __name__ == '__main__':
    main()
