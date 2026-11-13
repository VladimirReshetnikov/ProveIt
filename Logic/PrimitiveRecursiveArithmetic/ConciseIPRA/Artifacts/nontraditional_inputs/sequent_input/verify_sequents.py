"""Finite regressions for the open-sequent interface; not the soundness proof."""
from pathlib import Path
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

HERE = Path(__file__).resolve().parent
BASE = HERE / 'baseline'
UPSTREAM = BASE / 'code/checker_bytes460.py'
CANDIDATE = HERE / 'checker_sequent458.py'


def run(program, text, optimized=False):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command += ['-O']
    command += [str(program)]
    p = subprocess.run(command, input=text, text=True, capture_output=True, timeout=10)
    return p.returncode == 0 and p.stdout == 'ACCEPT\n'


def metrics(path):
    tree = ast.parse(path.read_text())
    normalized = ast.unparse(tree) + '\n'
    ignored = {tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL, tokenize.INDENT,
               tokenize.DEDENT, tokenize.COMMENT, tokenize.ENCODING}
    tokens = sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized).readline))
    return {'tokens': tokens, 'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(normalized.encode()),
            'sha256': hashlib.sha256(normalized.encode()).hexdigest()}


def main():
    examples = HERE / 'sequent_examples'
    examples.mkdir(exist_ok=True)
    control_source = UPSTREAM.read_text().replace('c([0], *q())',
        'g, a, k = q()\nc([0] + g, a, k)')
    control = HERE / 'sequent_control_adapter.py'
    control.write_text(ast.unparse(ast.parse(control_source)) + '\n')
    assert control_source != UPSTREAM.read_text()
    results = []
    cases = json.loads((BASE / 'fixtures/compact_cases.json').read_text())
    for case in cases:
        original = (BASE / case['file']).read_text()
        data = json.loads(original)
        if case['name'] == 'malformed_header':
            translated = original
        else:
            a, k = data[-1]
            data[-1] = [[], a, k]
            translated = json.dumps(data)
        for optimized in (False, True):
            expected = case['expected_candidate']
            old = run(UPSTREAM, original, optimized)
            new = run(CANDIDATE, translated, optimized)
            adapted = run(control, translated, optimized)
            results.append({'case': case['name'], 'optimized': optimized,
                            'expected': expected, 'old': old, 'new': new,
                            'adapted_control': adapted,
                            'passed': old == new == adapted == expected})
    truth, falsehood = [0, 0], [0, [0]]
    dummy = [0, 0, 0, 0]
    s, u = [0, [0], 0], [0]
    major, template = [s, u], [5, 0]
    new_cases = {
        'identity_false_assumption': ([dummy, [[falsehood], falsehood, 0]], True),
        'identity_truth_assumption': ([dummy, [[truth], truth, 0]], True),
        'unrelated_assumption_rejected': ([dummy] * 4 + [[[truth], falsehood, 0]], False),
        'false_conclusion_empty_context': ([dummy] * 4 + [[[], falsehood, 0]], False),
        'transport_from_two_assumptions': ([dummy, dummy, [s, u, template, major],
                                           [[major, [s, 0]], [u, 0], 0]], True),
        'transport_missing_major_rejected': ([dummy, dummy, [s, u, template, major],
                                             [[[s, 0]], [u, 0], 0]], False),
        'transport_missing_minor_rejected': ([dummy, dummy, [s, u, template, major],
                                             [[major], [u, 0], 0]], False),
        'future_parameter_goal_rejected': ([dummy] * 4 + [[[[0, 0]], [-1, 0], 0]], False),
    }
    for name, (data, expected) in new_cases.items():
        text = json.dumps(data, separators=(',', ':')) + '\n'
        (examples / (name + '.json')).write_text(text)
        for optimized in (False, True):
            new = run(CANDIDATE, text, optimized)
            adapted = run(control, text, optimized)
            results.append({'case': name, 'optimized': optimized, 'expected': expected,
                            'new': new, 'adapted_control': adapted,
                            'passed': new == adapted == expected})
    zero = json.loads((BASE / 'fixtures/compact/computation_zero_local.json').read_text())
    zero[-1] = [[], *zero[-1]]
    (examples / 'zero_computation_empty_context.json').write_text(json.dumps(zero) + '\n')
    report = {'python': sys.version, 'candidate': metrics(CANDIDATE),
              'baseline': metrics(UPSTREAM), 'cases': len(cases) + len(new_cases),
              'executions': 6 * len(cases) + 4 * len(new_cases),
              'failures': [r for r in results if not r['passed']], 'results': results}
    (HERE / 'sequent_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if report['failures']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
