"""Finite implementation checks; these do not replace the mathematical proof."""
import ast
import copy
import gzip
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

import checker
from proofs import H0, fixtures, hypothesis, reflexivity, symmetry, transitivity
from translate import checked_round_trip, verify_ce5


ROOT = Path(__file__).resolve().parent


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def metrics(path):
    tree = ast.parse(path.read_text())
    if (isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    source = ast.unparse(tree) + '\n'
    excluded = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
                tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {'bytes': len(source.encode()),
            'tokens': sum(t.type not in excluded for t in tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast': len(list(ast.walk(tree))),
            'gzip9': len(gzip.compress(source.encode(), compresslevel=9, mtime=0))}


def main():
    good = fixtures()
    for name, data in good.items():
        try:
            checker.check(data)
        except Exception as exc:
            raise AssertionError(name) from exc
        checked_round_trip(data)
    ce5_count = verify_ce5(ROOT / 'reference_ce5.py')
    # Open-sequent checks exercise equality assumptions independently of
    # arithmetic truth in the standard model.
    s, t, u = -1, -2, -3
    context = [(H0, [s, t]), (H0, [t, u])]
    assert checker.derive(symmetry(s, t, hypothesis(0), 3, 2), context, 3) == [t, s]
    assert checker.derive(transitivity(s, t, u, hypothesis(0), hypothesis(1), 3, 2), context, 3) == [s, u]
    bad = {
        'false_equation': {'goal': [0, [0, 0]], 'proof': ['c', [0, 0, 0]]},
        'successor_not_iterator': {'goal': [0, 0], 'proof': ['c', [0, 0]]},
        'iterator_counter_not_successor': {'goal': [0, 0], 'proof': ['c', [[0, 0, 0], 0, 0]]},
        'boolean_term': {'goal': [False, 0], 'proof': ['c', [0, 0, 0]]},
        'loose_bound_variable': {'goal': [1, 1], 'proof': reflexivity(1)},
        'free_parameter': {'goal': [-1, -1], 'proof': reflexivity(-1)},
        'negative_clause_index': {'goal': [0, 0], 'proof': ['u', -1, 0, ['c', [0, 0, 0]]]},
        'boolean_clause_index': {'goal': [0, 0], 'proof': ['u', False, 0, ['c', [0, 0, 0]]]},
        'missing_fields': {'goal': [0, 0]},
        'extra_fields': {'goal': [0, 0], 'proof': reflexivity(0), 'extra': 0},
        'extra_instruction_fields': {'goal': [0, 0], 'proof': ['c', [0, 0, 0], 0]},
        'unknown_tag': {'goal': [0, 0], 'proof': ['r', 0]},
    }
    for label, edit in [
        ('template_loose_index', lambda d: d['proof'].__setitem__(2, [2, 0])),
        ('template_fresh_leak', lambda d: d['proof'].__setitem__(2, [-1, 0])),
        ('equality_must_be_equation', lambda d: d['proof'].__setitem__(4, d['proof'][3])),
        ('major_must_be_D', lambda d: d['proof'].__setitem__(3, ['c', [0, 0, 0]])),
    ]:
        data = copy.deepcopy(good['reflexivity_zero'])
        edit(data)
        bad[label] = data
    for name, data in bad.items():
        try:
            checker.check(data)
        except Exception:
            pass
        else:
            raise AssertionError('accepted invalid fixture: ' + name)
    cli = 0
    for opt in ([], ['-O']):
        for expected, collection in [(True, good), (False, bad)]:
            for name, data in collection.items():
                result = subprocess.run([sys.executable, *opt, str(ROOT / 'checker.py')],
                                        input=json.dumps(data), text=True, capture_output=True)
                assert (result.returncode == 0) == expected, (opt, name, result.stdout)
                assert result.stdout.strip() == ('ACCEPT' if expected else 'REJECT')
                cli += 1
    examples = ROOT / 'examples'
    examples.mkdir(exist_ok=True)
    for name, data in good.items():
        (examples / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    output = {'positive': len(good), 'negative': len(bad), 'open_sequents': 2,
              'cli_runs': cli, 'exact_goal_control_round_trips': len(good),
              'ce5_forward_translations': ce5_count,
              'checker': metrics(ROOT / 'checker.py'),
              'matched_control': metrics(ROOT / 'control_separate.py'),
              'reference_ce5': metrics(ROOT / 'reference_ce5.py')}
    (ROOT / 'verification.json').write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
