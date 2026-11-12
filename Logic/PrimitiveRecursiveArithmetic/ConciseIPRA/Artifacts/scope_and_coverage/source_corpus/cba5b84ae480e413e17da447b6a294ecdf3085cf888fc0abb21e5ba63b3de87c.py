"""Offline reproduction; the measured checker imports none of this module."""
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def check_manifest():
    path = ROOT / 'MANIFEST.json'
    if not path.exists():
        return {'present': False, 'reason': 'Initial authoring run'}
    payload = json.loads(path.read_text())
    for row in payload['files']:
        data = (ROOT / row['path']).read_bytes()
        if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            raise ValueError('Manifest mismatch: ' + row['path'])
    return {'present': True, 'files_verified': len(payload['files'])}


def run(relative, *args):
    result = subprocess.run([sys.executable, str(ROOT / relative), *map(str, args)],
                            cwd=ROOT, text=True, capture_output=True, timeout=90)
    if result.returncode:
        print(result.stdout)
        print(result.stderr, file=sys.stderr)
        raise RuntimeError('Verification failed: ' + relative)


def main():
    integrity = check_manifest()
    run('tests/verify_symbolic.py')
    run('tests/check_boundaries.py')
    run('tests/check_control.py')
    run('tests/guard_control.py', ROOT / 'code/checker.py',
        ROOT / 'code/unrestricted_control.py')
    spec = importlib.util.spec_from_file_location('source_measure', ROOT / 'reference/source_measure.py')
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    names = ['reference/endpoint_compact.py', 'reference/minimum_ast.py',
             'reference/minimum_bytes.py', 'code/checker.py',
             'code/unrestricted_control.py', 'code/readable_checker.py']
    rows = [{'path': name, **measure.metrics(ROOT / name)} for name in names]
    measurements = {'python': platform.python_version(), 'implementation': platform.python_implementation(),
                    'frozen_corpus_envelope': {'normalized_tokens':287, 'ast_nodes':323, 'normalized_bytes':738},
                    'programs':rows}
    (ROOT / 'evidence/measurements.json').write_text(json.dumps(measurements,indent=2)+'\n')
    symbolic = json.loads((ROOT / 'tests/validation.json').read_text())
    boundary = json.loads((ROOT / 'tests/boundary_receipt.json').read_text())
    guard = json.loads((ROOT / 'tests/guard_control.json').read_text())
    control = json.loads((ROOT / 'tests/control_receipt.json').read_text())
    counts = {'symbolic_cli_runs':symbolic['cli_runs'],
              'independent_boundary_cli_runs':boundary['checks'],
              'guard_control_cli_runs':guard['cli_runs'],
              'unrestricted_control_cli_runs':control['cli_runs']}
    total = sum(counts.values())
    summary = {'passed':True, 'python':platform.python_version(), **counts,
               'total_cli_runs':total, 'symbolic_positive_cases':symbolic['positive'],
               'symbolic_negative_cases':symbolic['negative']}
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(summary,indent=2)+'\n')
    text = ('\\begin{quote}\n\\textbf{Recorded execution.} '
            f'{total} public checker runs passed: {symbolic["cli_runs"]} symbolic-certificate runs '
            f'({symbolic["positive"]} positive and {symbolic["negative"]} negative packets, each in two modes), '
            f'{boundary["checks"]} independent boundary runs, {control["cli_runs"]} full-fixture unrestricted-control runs, '
            f'and {guard["cli_runs"]} matched-guard runs. '
            'Both ordinary and optimized Python were exercised. '
            'The same direct compound-transport packet is rejected by the atomic kernel '
            'and accepted by its matched unrestricted control; expanded atomic proofs accept.\n'
            '\\end{quote}\n')
    (ROOT / 'evidence/validation_summary.tex').write_text(text)
    print(json.dumps({'manifest':integrity, **summary,
                      'atomic_metrics':rows[3], 'control_metrics':rows[4]},indent=2))


if __name__ == '__main__':
    main()
