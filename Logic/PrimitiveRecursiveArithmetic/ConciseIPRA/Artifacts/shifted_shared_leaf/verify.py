"""Reproduce the shifted/shared checker checks and trace translations.

Finite tests are supplementary evidence, not proofs of soundness,
completeness, equiconsistency, or bi-interpretability.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from measure import measure


def execute(program, payload, optimized=False):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / program))
    try:
        result = subprocess.run(command, input=payload, capture_output=True, timeout=25)
        return {'accepted': result.returncode == 0 and result.stdout == b'ACCEPT\n',
                'exit_code': result.returncode,
                'exception': result.stderr.decode(errors='replace').splitlines()[-1]
                             if result.stderr else ''}
    except subprocess.TimeoutExpired:
        return {'accepted': False, 'exit_code': None, 'exception': 'TIMEOUT'}


def main():
    code = (ROOT / 'code/checker.py').read_text()
    control = (ROOT / 'controls/shared_leaf469.py').read_text()
    expected_source = (control.replace('d=0', 'd=2').replace('d=3', 'd=5')
                       .replace('u, t], 3)', 'u, t], 5)')
                       .replace('i(*a, t, 2)', 'i(*a, t, 4)')
                       .replace('c([[]], *q())', 'c([0], *q())'))
    if code != expected_source:
        raise AssertionError('The declared five-site source transformation does not match')
    metrics = measure(ROOT / 'code/checker.py')
    if (metrics['tokens'], metrics['ast_nodes'], metrics['normalized_bytes']) != (271, 305, 468):
        raise AssertionError(('Unexpected metric vector', metrics))

    results = []
    programs = ['code/checker.py', 'code/readable_checker.py']

    def run_case(program, fixture, payload, expected, kind):
        for optimized in (False, True):
            results.append({'program': program, 'fixture': fixture, 'kind': kind,
                            'expected': expected, 'optimized': optimized,
                            **execute(program, payload, optimized)})

    for path in sorted((ROOT / 'fixtures/shared468').glob('*.json')):
        expected = not path.name.startswith(('reject_', 'future_witness'))
        payload = path.read_bytes()
        for program in programs:
            run_case(program, path.name, payload, expected, 'supplied-shifted-shared')
        if expected:
            altered = json.loads(payload)
            altered[-1] = [[0, [0]], 0]
            bad = json.dumps(altered).encode()
            for program in programs:
                run_case(program, path.name, bad, False, 'false-public-goal')

    converter_path = ROOT / 'code/translate_offset_to_shared.py'
    spec = importlib.util.spec_from_file_location('trace_converter', converter_path)
    converter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(converter)
    translations = []
    for path in sorted((ROOT / 'fixtures/offset472').glob('*.json')):
        original = json.loads(path.read_text())
        translated, stats = converter.convert(original)
        if original[-1] != translated[-1]:
            raise AssertionError(('Changed public goal or initial scope', path.name))
        run_case('controls/offset472.py', path.name, path.read_bytes(), True,
                 'source-before-padding')
        payload = (json.dumps(translated, separators=(',', ':')) + '\n').encode()
        for program in programs:
            run_case(program, path.name, payload, True, 'successful-trace-padding')
        translations.append({'fixture': path.name, 'root_unchanged': True, **stats})

    failures = [r for r in results if r['expected'] != r['accepted']
                or r['exception'] == 'TIMEOUT']
    report = {'python': sys.version, 'metrics': metrics,
              'executions': len(results), 'unexpected_outcomes': len(failures),
              'declared_source_transformation_matches': True,
              'translations': translations, 'results': results, 'failures': failures,
              'proof_status': 'Finite executable evidence; universal claims require the report proofs.'}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'executions': len(results), 'translations': len(translations),
                      'unexpected_outcomes': len(failures)}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
