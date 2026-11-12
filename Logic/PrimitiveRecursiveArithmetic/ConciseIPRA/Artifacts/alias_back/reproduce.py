"""Reproduce all local proof checks and complete-module measurements offline."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import hashlib
import json
import os
import platform
import subprocess
import sys
from measure import measure

ROOT = Path(__file__).resolve().parent
PROGRAMS = [
    'controls/tokens248.py', 'controls/ast270.py', 'controls/checker_487.py',
    'code/checker_479.py',
    'raw_basis/code/raw_template_matched.py', 'raw_basis/code/raw_alias.py',
    'raw_basis/code/raw_template_small.py', 'raw_basis/code/raw_alias_small.py',
    'supplement/two_field/code/tree_control.py',
    'supplement/two_field/code/two_fields_compact.py',
]
EXPECTED = [(248,277,609),(254,270,608),(276,308,487),(272,304,479),
            (764,883,2918),(825,966,3149),(716,838,2683),(773,916,2903),
            (629,732,1715),(609,699,1644)]
SUITES = ['verify_byte.py', 'raw_basis/verify.py', 'equality_audit/verify.py',
          'supplement/two_field/verify.py']


def run_suite(relative):
    path = ROOT / relative
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    result = subprocess.run([sys.executable, '-B', str(path)], cwd=path.parent,
                            env=env, text=True, capture_output=True, timeout=120)
    if result.returncode:
        raise RuntimeError(relative + '\n' + result.stdout + '\n' + result.stderr)
    return {'suite': relative, 'exit_code': 0, 'summary': json.loads(result.stdout)}


def main():
    provenance = json.loads((ROOT / 'evidence/SOURCE_PROVENANCE.json').read_text())
    for source in provenance['frozen_sources']:
        data = (ROOT / source['local']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if blob != source['git_blob_sha1'] or hashlib.sha256(data).hexdigest() != source['sha256']:
            raise AssertionError(('frozen source identity', source['local']))
    metrics = {name: measure(ROOT / name) for name in PROGRAMS}
    if platform.python_version() == '3.12.14':
        for name, expected in zip(PROGRAMS, EXPECTED):
            if tuple(metrics[name].values()) != expected:
                raise AssertionError(('measurement changed', name, metrics[name], expected))
    with ThreadPoolExecutor(max_workers=4) as pool:
        suites = list(pool.map(run_suite, SUITES))
    byte = json.loads((ROOT / 'evidence/byte_validation.json').read_text())
    raw = json.loads((ROOT / 'raw_basis/evidence/validation.json').read_text())
    eq = json.loads((ROOT / 'equality_audit/evidence.json').read_text())
    stream = json.loads((ROOT / 'supplement/two_field/evidence/verification.json').read_text())
    report = {'python': platform.python_version(), 'commit': provenance['commit'],
              'frozen_sources_verified': len(provenance['frozen_sources']),
              'metrics': metrics, 'suites': suites,
              'process_counts': {'byte': byte['process_executions'],
                                 'raw': raw['process_runs'],
                                 'equality': eq.get('process_runs', eq.get('process_executions', eq.get('runs'))),
                                 'two_field': stream['runs']},
              'failures': 0}
    counts = report['process_counts']
    if all(isinstance(n, int) for n in counts.values()):
        report['total_process_executions'] = sum(counts.values())
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(report, indent=2) + '\n')
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('metrics','suites')}, indent=2))


if __name__ == '__main__':
    main()
