"""Recompute complete-module metrics and rerun the focused verification suites."""
from pathlib import Path
import importlib.util
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CHECKERS = ROOT / 'code' / 'checkers'


def main():
    for script in ('verify.py', 'verify_profiles.py'):
        subprocess.run([sys.executable, str(CHECKERS / script)],
                       cwd=CHECKERS, check=True)
    subprocess.run([sys.executable, str(ROOT / 'tools' / 'verify_pattern.py')],
                   cwd=ROOT, check=True)
    specification = importlib.util.spec_from_file_location('measure_checkers', CHECKERS / 'verify.py')
    module = importlib.util.module_from_spec(specification)
    sys.path.insert(0, str(CHECKERS))
    specification.loader.exec_module(module)
    names = ['checker_tokens_json.py', 'checker_ast_json.py',
             'checker.py', 'checker_ast_jsonl.py', 'control.py',
             'control_tokens248_json.py', 'control_ast268_json.py',
             'control_tokens241_jsonl.py', 'control_ast262_jsonl.py']
    metrics = {name: module.measure(CHECKERS / name) for name in names}
    expected = json.loads((ROOT / 'evidence' / 'measurements.json').read_text())['programs']
    for name in names:
        assert metrics[name] == expected[name], (name, metrics[name], expected[name])
    from translate import forward
    readable_rows = []
    for fixture in sorted((CHECKERS / 'fixtures').glob('*.json')):
        expected_result = not fixture.name.startswith('future_witness')
        certificate = forward(json.loads(fixture.read_text()))
        accepted = module.execute('readable_checker.py', certificate, False)
        assert accepted == expected_result, (fixture.name, accepted, expected_result)
        readable_rows.append({'fixture': fixture.name, 'expected': expected_result,
                              'accepted': accepted})
    readable_result = {'python': sys.version, 'cases': readable_rows,
                       'process_executions': len(readable_rows),
                       'all_expectations_met': True}
    (ROOT / 'evidence' / 'readable_verification.json').write_text(
        json.dumps(readable_result, indent=2) + '\n')
    print(json.dumps({'python': sys.version, 'measurements_match': True,
                      'readable_fixture_checks': len(readable_rows),
                      'programs': metrics}, indent=2))


if __name__ == '__main__':
    main()
