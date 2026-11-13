"""Reproduce the exact 6-byte refinement; no network or nonstandard packages.

Every assertion in this harness concerns the submitted modules or the one
rewritten expression. The finite regressions do not prove iPRA soundness.
"""
from pathlib import Path
import ast
import copy
import hashlib
import io
import json
import subprocess
import sys
import tokenize

HERE = Path(__file__).resolve().parent
OLD = HERE.parent / 'controls/retained_bytes.py'
NEW = HERE.parent / 'code/checker.py'
BEFORE = 'j & 2 if d % 2 else 5 - len(a)'
AFTER = '(5 - len(a), j & 2)[d % 2]'
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def metrics(path):
    tree = ast.parse(path.read_text())
    text = ast.unparse(tree) + '\n'
    return {'tokens': sum(t.type not in SKIP for t in
                          tokenize.generate_tokens(io.StringIO(text).readline)),
            'ast_nodes': len(list(ast.walk(tree))),
            'normalized_bytes': len(text.encode()),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def kernel(path):
    nodes = []
    for node in ast.parse(path.read_text()).body:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            break
        nodes.append(node)
    return compile(ast.Module(body=nodes, type_ignores=[]), str(path), 'exec')


def accepts(code, certificate):
    namespace = {}
    exec(code, namespace)
    parsed = json.loads(json.dumps(certificate, allow_nan=True))
    try:
        namespace['q'] = parsed.pop
        namespace['c']([[]], namespace['q']())
        return True
    except Exception:
        return False


def main():
    original = OLD.read_text()
    candidate = NEW.read_text()
    assert original.count(BEFORE) == 1
    expected_tree = ast.parse(original.replace(BEFORE, AFTER))
    assert ast.dump(expected_tree) == ast.dump(ast.parse(candidate))
    measured = {'control': metrics(OLD), 'candidate': metrics(NEW)}
    assert [measured['candidate'][k] for k in
            ('tokens', 'ast_nodes', 'normalized_bytes')] == [310, 358, 576]

    # The proof establishes these equalities for all integer depths and
    # list lengths; these boundary tests catch a mistaken source rewrite.
    arithmetic = 0
    for depth in range(-17, 42):
        for arity in range(10):
            for index in range(arity):
                assert (index & 2 if depth % 2 else 5 - arity) == (
                    5 - arity, index & 2)[depth % 2]
                arithmetic += 1

    positives = json.loads((HERE / 'fixtures/native_positives.json').read_text())['cases']
    cases = [(c['name'], c['certificate'], True) for c in positives]
    for case in positives:
        doc = case['certificate']
        for name, goal in [('false_zero_one', [1, [1]]),
                           ('false_one_zero', [[1], 1])]:
            cases.append((case['name'] + '_' + name, doc[:-1] + [goal], False))
    base = positives[0]['certificate']
    invalid_goals = [0, 1, [], [0, 1], [2, 1], [3, 1], [-1, 1],
                     [[3], [1]], [[5], [1]], [[1, 3, 1], 1],
                     [[1, 1, 5], 1], [1, 1, 1], [[], 1],
                     True, 1.5, None, 'x', {}]
    for index, goal in enumerate(invalid_goals):
        cases.append(('invalid_public_' + str(index), base[:-1] + [goal], False))
    for index, packet in enumerate([[], [0], [0, 1], [0, 1, 2, 3, 4], 0, None]):
        cases.append(('invalid_packet_' + str(index), base[:-2] + [packet, base[-1]], False))
    for name in ('capture_four', 'entry_capture'):
        doc = json.loads((HERE / ('fixtures/' + name + '.json')).read_text())
        cases.append((name, doc, False))
    # Unused JSON material is deliberately permitted by the upstream contract.
    for index, unused in enumerate([None, False, True, 1.5, '', {}, 'unused', float('nan')]):
        cases.append(('unused_prefix_' + str(index), [unused] + base, True))
    codes = [kernel(OLD), kernel(NEW)]
    results = []
    for name, doc, expected in cases:
        verdicts = [accepts(code, doc) for code in codes]
        results.append({'name': name, 'expected': expected, 'verdicts': verdicts})
        assert verdicts == [expected, expected], results[-1]

    # Full CLI and optimized execution: includes both computation clauses,
    # compound logic, used-hypothesis induction, equality transport and capture.
    selected = {c['name']: c for c in positives}
    process_cases = [(name, selected[name]['certificate'], True) for name in
                     ('computation_zero_local', 'computation_successor_local',
                      'compound_implication_elimination_local',
                      'guarded_induction_with_used_hypothesis_local',
                      'derived_zero_source_equational_transport_local')]
    process_cases.extend((name, doc, expected) for name, doc, expected in cases
                         if name in ('capture_four', 'entry_capture', 'invalid_public_8'))
    process_results = []
    for name, doc, expected in process_cases:
        for program in (OLD, NEW):
            for optimized in (False, True):
                result = subprocess.run([sys.executable, *(['-O'] if optimized else []),
                                         str(program)], input=json.dumps(doc), text=True,
                                        capture_output=True, timeout=30)
                accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
                record = {'case': name, 'program': program.name,
                          'optimized': optimized, 'accepted': accepted}
                process_results.append(record)
                assert accepted == expected, record
    receipt = {'python': sys.version, 'metrics': measured,
               'exact_source_transformation': True,
               'offset_identity_boundary_checks': arithmetic,
               'differential_cases': results, 'process_results': process_results,
               'failures': []}
    (HERE.parent / 'evidence/test_results.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'metrics': measured, 'differential_cases': len(results),
                      'process_runs': len(process_results), 'failures': []}, indent=2))


if __name__ == '__main__':
    main()
