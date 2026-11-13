"""Run substantive supplied certificates against the delivered standalone modules.

The universal correspondence proofs are in the report and review notes.
Finite tests do not prove soundness or bi-interpretability.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def execute(program, payload, optimized=False):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / 'code' / program))
    try:
        result = subprocess.run(command, input=payload, capture_output=True, timeout=25)
        return {'accepted': result.returncode == 0 and result.stdout == b'ACCEPT\n',
                'exit_code': result.returncode,
                'exception': result.stderr.decode(errors='replace').splitlines()[-1]
                             if result.stderr else ''}
    except subprocess.TimeoutExpired:
        return {'accepted': False, 'exit_code': None, 'exception': 'TIMEOUT'}


def load_translator(name):
    path = ROOT / 'code' / name
    spec = importlib.util.spec_from_file_location(name[:-3], path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    results, translations = [], []
    groups = [('bytes', 'checker_bytes.py'), ('tokens', 'checker_tokens.py'),
              ('ast', 'checker_ast.py'), ('bytes', 'readable_checker.py')]
    for group, program in groups:
        for path in sorted((ROOT / 'fixtures' / group).glob('*')):
            payload = path.read_bytes()
            expected = not (path.name.startswith(('reject_', 'future_witness'))
                            or path.name == 'direct_false_zero_initializer.jsonl')
            for optimized in (False, True):
                row = {'program': program, 'fixture': str(path.relative_to(ROOT)),
                       'kind': 'supplied', 'expected': expected, 'optimized': optimized,
                       **execute(program, payload, optimized)}
                results.append(row)
                if path.name.startswith('future_witness'):
                    if not row['exception'].startswith('TypeError:'):
                        raise AssertionError(('scope attack did not fail during scope opening', row))
            if expected:
                if group == 'bytes':
                    changed = json.loads(payload)
                    changed[-1] = [[0, [0]], 0]
                    bad = json.dumps(changed).encode()
                else:
                    lines = payload.decode().splitlines()
                    bad = ('[0,[0]]\n' + '\n'.join(lines[1:]) + '\n').encode()
                for optimized in (False, True):
                    results.append({'program': program, 'fixture': path.name,
                                    'kind': 'false-public-goal', 'expected': False,
                                    'optimized': optimized, **execute(program, bad, optimized)})
    for path in sorted((ROOT / 'fixtures' / 'strict').glob('*.json')):
        expected = path.name in {'computation_zero_local.json', 'compound_implication_elimination_local.json'}
        for optimized in (False, True):
            results.append({'program': 'strict_incumbent616.py', 'fixture': path.name,
                            'kind': 'unchanged-strict-companion', 'expected': expected,
                            'optimized': optimized,
                            **execute('strict_incumbent616.py', path.read_bytes(), optimized)})
    for translator_name, group in [('translate_tokens.py', 'tokens'), ('translate_ast.py', 'ast')]:
        translator = load_translator(translator_name)
        for path in sorted((ROOT / 'fixtures/source_stream').glob('*.jsonl')):
            output, statistics = translator.convert(path.read_text())
            target = ROOT / 'fixtures' / group / path.name
            if output != target.read_text():
                raise AssertionError(('translation is not reproducible', str(target)))
            translations.append({'translator': translator_name, 'source': path.name,
                                 'exact_output_match': True, 'statistics': statistics})
    translator = load_translator('translate_bytes.py')
    for path in sorted((ROOT / 'fixtures/source_bytes').glob('*.json')):
        output, statistics = translator.convert(json.loads(path.read_text()))
        name = path.name.removeprefix('compact_context__').replace('_local.json', '.json')
        target = ROOT / 'fixtures/bytes' / name
        if output != json.loads(target.read_text()):
            raise AssertionError(('byte translation is not reproducible', name))
        translations.append({'translator': 'translate_bytes.py', 'source': path.name,
                             'exact_output_match': True, 'statistics': statistics})
    failures = [r for r in results if r['accepted'] != r['expected'] or r['exception'] == 'TIMEOUT']
    report = {'python': sys.version.split()[0], 'executions': len(results),
              'failures': failures, 'results': results,
              'reproduced_translations': translations,
              'proof_status': 'Finite executable evidence; universal theorems are proved in the report.'}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'executions': len(results), 'reproduced_translations': len(translations),
                      'unexpected_outcomes': len(failures)}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
